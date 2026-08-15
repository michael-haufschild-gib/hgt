import GaloisForLFunctions.RHTower.XiShiftedHardEdgeTightness
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeBernstein
import GaloisForLFunctions.HTGeometry.L2GridApproximation

/-!
# Strong `L²` precompactness of the normalized hard-edge family

The two Kolmogorov–Riesz conditions for the rational hard-edge family are now formal: uniform
tightness in the height is `routeUHardEdge_tail_le`, and the uniform `L²` bound on the derivative is
the rational Bernstein estimate.  Feeding them into the grid criterion gives that the normalized
nonpositive family of bounded scaled degree is totally bounded in `L²(ℝ)`, hence has a strongly
convergent subsequence.
-/

open MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## The derivative in a Chebyshev frame -/

/-- The derivative of the rational hard-edge test, in a Chebyshev frame for its angular
polynomial. -/
def routeUHardEdgeTestDeriv (a : ℝ) (N : ℕ) (b : ℕ → ℝ) (x : ℝ) : ℝ :=
  halfCosPolyDeriv N (halfShiftCoeff N b) (routeUHardEdgeInverseChart a x)
    * (2 * a / (a ^ 2 + x ^ 2))

theorem continuous_halfCosPolyDeriv (M : ℕ) (c : ℕ → ℝ) : Continuous (halfCosPolyDeriv M c) := by
  unfold halfCosPolyDeriv
  refine continuous_finsetSum _ fun j _ => ?_
  exact continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))

theorem abs_halfCosPolyDeriv_le (M : ℕ) (c : ℕ → ℝ) (θ : ℝ) :
    |halfCosPolyDeriv M c θ| ≤ ∑ j ∈ Finset.range (M + 1), |c j| * ((j : ℝ) + 1 / 2) := by
  unfold halfCosPolyDeriv
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_mul, abs_neg, abs_mul]
  have hsin : |Real.sin (((j : ℝ) + 1 / 2) * θ)| ≤ 1 := Real.abs_sin_le_one _
  have hj : |((j : ℝ) + 1 / 2)| = (j : ℝ) + 1 / 2 := by
    refine abs_of_nonneg ?_
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  rw [hj]
  have hnn : (0 : ℝ) ≤ |c j| * ((j : ℝ) + 1 / 2) := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have h2 : (0 : ℝ) ≤ |c j| := abs_nonneg _
    positivity
  nlinarith [abs_nonneg (Real.sin (((j : ℝ) + 1 / 2) * θ)), abs_nonneg (c j)]

theorem continuous_routeUHardEdgeInverseChart (a : ℝ) :
    Continuous (routeUHardEdgeInverseChart a) := by
  unfold routeUHardEdgeInverseChart
  exact continuous_const.mul (Real.continuous_arctan.comp (continuous_id.div_const a))

theorem continuous_routeUHardEdgeTestDeriv {a : ℝ} (ha : 0 < a) (N : ℕ) (b : ℕ → ℝ) :
    Continuous (routeUHardEdgeTestDeriv a N b) := by
  unfold routeUHardEdgeTestDeriv
  refine Continuous.mul ?_ ?_
  · exact (continuous_halfCosPolyDeriv N _).comp (continuous_routeUHardEdgeInverseChart a)
  · refine Continuous.div continuous_const (by fun_prop) fun x => ?_
    have h : (0 : ℝ) < a ^ 2 + x ^ 2 := by positivity
    exact ne_of_gt h

theorem hasDerivAt_routeUHardEdgeTestDeriv {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ) {N : ℕ}
    {b : ℕ → ℝ}
    (hb : routeUHardEdgeAngularPoly a p
      = ∑ j ∈ Finset.range (N + 1),
        Polynomial.C (b j) * Polynomial.Chebyshev.T ℝ (j : ℤ)) (x : ℝ) :
    HasDerivAt (routeUHardEdgeRationalTest a p) (routeUHardEdgeTestDeriv a N b x) x :=
  hasDerivAt_routeUHardEdgeRationalTest ha p hb x

theorem integrable_routeUHardEdgeTestDeriv_sq {a : ℝ} (ha : 0 < a) (N : ℕ) (b : ℕ → ℝ) :
    Integrable (fun x : ℝ => routeUHardEdgeTestDeriv a N b x ^ 2) volume := by
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ∑ j ∈ Finset.range (N + 1),
      |halfShiftCoeff N b j| * ((j : ℝ) + 1 / 2) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    refine Finset.sum_nonneg fun j _ => ?_
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have h2 : (0 : ℝ) ≤ |halfShiftCoeff N b j| := abs_nonneg _
    positivity
  have hmaj : Integrable (fun x : ℝ => (2 * a * B) ^ 2 * (((a ^ 2 + x ^ 2) ^ 2)⁻¹)) volume :=
    (integrable_inv_sq_add_sq_sq ha).const_mul _
  refine hmaj.mono' ?_ ?_
  · exact ((continuous_routeUHardEdgeTestDeriv ha N b).pow 2).aestronglyMeasurable
  filter_upwards with x
  have hpos : (0 : ℝ) < a ^ 2 + x ^ 2 := by positivity
  have hbound : |routeUHardEdgeTestDeriv a N b x| ≤ 2 * a * B * (a ^ 2 + x ^ 2)⁻¹ := by
    rw [routeUHardEdgeTestDeriv, abs_mul]
    have h1 := abs_halfCosPolyDeriv_le N (halfShiftCoeff N b)
      (routeUHardEdgeInverseChart a x)
    rw [← hBdef] at h1
    have h2 : |2 * a / (a ^ 2 + x ^ 2)| = 2 * a * (a ^ 2 + x ^ 2)⁻¹ := by
      rw [abs_of_nonneg (by positivity)]
      ring
    rw [h2]
    have h3 : (0 : ℝ) ≤ 2 * a * (a ^ 2 + x ^ 2)⁻¹ := by positivity
    nlinarith [abs_nonneg (halfCosPolyDeriv N (halfShiftCoeff N b)
      (routeUHardEdgeInverseChart a x))]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hsq : routeUHardEdgeTestDeriv a N b x ^ 2 = |routeUHardEdgeTestDeriv a N b x| ^ 2 :=
    (sq_abs _).symm
  rw [hsq]
  have hstep := pow_le_pow_left₀ (abs_nonneg (routeUHardEdgeTestDeriv a N b x)) hbound 2
  refine le_trans hstep (le_of_eq ?_)
  rw [mul_pow, ← inv_pow]

theorem continuous_routeUHardEdgeRationalTest {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ) :
    Continuous (routeUHardEdgeRationalTest a p) := by
  have hpos : ∀ x : ℝ, (0 : ℝ) < a ^ 2 + x ^ 2 := fun x =>
    add_pos_of_pos_of_nonneg (pow_pos ha 2) (sq_nonneg x)
  unfold routeUHardEdgeRationalTest
  refine Continuous.mul ?_ ?_
  · refine Continuous.div continuous_const (Real.continuous_sqrt.comp (by fun_prop)) fun x => ?_
    exact ne_of_gt (Real.sqrt_pos.mpr (hpos x))
  · exact p.continuous.comp (Continuous.inv₀ (by fun_prop) fun x => ne_of_gt (hpos x))

theorem memLp_routeUHardEdgeRationalTest {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ) :
    MemLp (routeUHardEdgeRationalTest a p) 2 (volume : Measure ℝ) := by
  refine (memLp_two_iff_integrable_sq ?_).2 (integrable_routeUHardEdgeRationalTest_sq ha p)
  exact (continuous_routeUHardEdgeRationalTest ha p).aestronglyMeasurable


/-! ## The precompactness theorem -/

/-- **(CSHC.5) Strong `L²` precompactness.**  The normalized nonpositive rational hard-edge family
of bounded scaled degree is totally bounded in `L²(ℝ)`. -/
theorem totallyBounded_routeUHardEdgeFamily {C : ℝ} (hC : 0 < C)
    {ι : Type*} {a : ι → ℝ} {p : ι → Polynomial ℝ} {N : ι → ℕ}
    (ha : ∀ i : ι, 4 ≤ a i)
    (hN : ∀ i : ι, (routeUHardEdgeAngularPoly (a i) (p i)).natDegree ≤ N i)
    (hNC : ∀ i : ι, ((N i : ℕ) : ℝ) ≤ C * a i)
    (hnorm : ∀ i : ι, (∫ x : ℝ, routeUHardEdgeRationalTest (a i) (p i) x ^ 2) = 1)
    (hW : ∀ i : ι, (∑' q : XiZeroCopy,
      routeUHardEdgeRationalTestSq (a i) (p i) (xiSpectralPoint q)).re ≤ 0) :
    TotallyBounded (Set.range fun i : ι =>
      MemLp.toLp (routeUHardEdgeRationalTest (a i) (p i))
        (memLp_routeUHardEdgeRationalTest (by linarith [ha i]) (p i))) := by
  have ha0 : ∀ i : ι, (0 : ℝ) < a i := fun i => by linarith [ha i]
  choose b hb using fun i : ι => exists_chebyshev_expansion (N i)
    (routeUHardEdgeAngularPoly (a i) (p i)) (hN i)
  refine totallyBounded_toLp_of_tight_deriv
    (f' := fun i => routeUHardEdgeTestDeriv (a i) (N i) (b i))
    (Mb := 1) (D := 4 * (C + 1 / 8) ^ 2)
    (fun i => memLp_routeUHardEdgeRationalTest (by linarith [ha i]) (p i))
    (fun i => hasDerivAt_routeUHardEdgeTestDeriv (ha0 i) (p i) (hb i))
    (fun i => continuous_routeUHardEdgeTestDeriv (ha0 i) _ _)
    (fun i => le_of_eq (hnorm i))
    (by positivity)
    (fun i => integrable_routeUHardEdgeTestDeriv_sq (ha0 i) _ _) ?_ ?_
  · -- the uniform Bernstein bound
    intro i
    have hbase := integral_deriv_routeUHardEdgeRationalTest_sq_le (ha0 i) (p i) (hb i)
    rw [hnorm i, mul_one] at hbase
    refine le_trans hbase ?_
    have haipos : (0 : ℝ) < a i := ha0 i
    have hratio : ((N i : ℕ) : ℝ) + 1 / 2 ≤ (C + 1 / 8) * a i := by
      have h1 : ((N i : ℕ) : ℝ) ≤ C * a i := hNC i
      have h2 : (1 : ℝ) / 2 ≤ (1 / 8) * a i := by linarith [ha i]
      linarith
    have hnn : (0 : ℝ) ≤ ((N i : ℕ) : ℝ) + 1 / 2 := by
      have : (0 : ℝ) ≤ ((N i : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hsq : (((N i : ℕ) : ℝ) + 1 / 2) ^ 2 ≤ ((C + 1 / 8) * a i) ^ 2 :=
      pow_le_pow_left₀ hnn hratio 2
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (a i)]
  · -- uniform tightness
    intro ε hε
    obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = max (routeUTightnessConst C) 1 := ⟨_, rfl⟩
    have hB1 : (1 : ℝ) ≤ B := by rw [hBdef]; exact le_max_right _ _
    have hBT : routeUTightnessConst C ≤ B := by rw [hBdef]; exact le_max_left _ _
    have hB0 : (0 : ℝ) < B := by linarith
    refine ⟨Real.exp (B / ε), Real.exp_pos _, fun i => ?_⟩
    have hR0 : (0 : ℝ) < Real.exp (B / ε) := Real.exp_pos _
    have hlog : B / ε ≤ Real.log (2 + Real.exp (B / ε)) := by
      have h1 : Real.log (Real.exp (B / ε)) ≤ Real.log (2 + Real.exp (B / ε)) :=
        Real.log_le_log hR0 (by linarith)
      rwa [Real.log_exp] at h1
    have hlogpos : (0 : ℝ) < Real.log (2 + Real.exp (B / ε)) := by
      have : (0 : ℝ) < B / ε := by positivity
      linarith
    have htail := routeUHardEdge_tail_le hC (ha i) (p i) (hN i) (hNC i) (hW i)
      (le_of_lt hR0)
    rw [hnorm i, mul_one] at htail
    refine le_trans htail ?_
    rw [div_le_iff₀ hlogpos]
    have hstep : B ≤ ε * Real.log (2 + Real.exp (B / ε)) := by
      have := mul_le_mul_of_nonneg_left hlog hε.le
      rw [mul_div_cancel₀ B (ne_of_gt hε)] at this
      exact this
    linarith


/-- **(CSHC.5) A strongly convergent subsequence with nonzero limit.**  Every normalized nonpositive
sequence of bounded scaled degree has an `L²`-convergent subsequence whose limit is a unit
vector. -/
theorem exists_subseq_tendsto_routeUHardEdge {C : ℝ} (hC : 0 < C)
    {a : ℕ → ℝ} {p : ℕ → Polynomial ℝ} {N : ℕ → ℕ}
    (ha : ∀ n : ℕ, 4 ≤ a n)
    (hN : ∀ n : ℕ, (routeUHardEdgeAngularPoly (a n) (p n)).natDegree ≤ N n)
    (hNC : ∀ n : ℕ, ((N n : ℕ) : ℝ) ≤ C * a n)
    (hnorm : ∀ n : ℕ, (∫ x : ℝ, routeUHardEdgeRationalTest (a n) (p n) x ^ 2) = 1)
    (hW : ∀ n : ℕ, (∑' q : XiZeroCopy,
      routeUHardEdgeRationalTestSq (a n) (p n) (xiSpectralPoint q)).re ≤ 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : Lp ℝ 2 (volume : Measure ℝ), ‖L‖ = 1 ∧
      Filter.Tendsto (fun k : ℕ =>
        MemLp.toLp (routeUHardEdgeRationalTest (a (φ k)) (p (φ k)))
          (memLp_routeUHardEdgeRationalTest (by linarith [ha (φ k)]) (p (φ k))))
        Filter.atTop (nhds L) := by
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ → Lp ℝ 2 (volume : Measure ℝ), F = fun n : ℕ =>
      MemLp.toLp (routeUHardEdgeRationalTest (a n) (p n))
        (memLp_routeUHardEdgeRationalTest (by linarith [ha n]) (p n)) := ⟨_, rfl⟩
  have htb : TotallyBounded (Set.range F) := by
    rw [hFdef]
    exact totallyBounded_routeUHardEdgeFamily hC ha hN hNC hnorm hW
  have hcomp : IsCompact (closure (Set.range F)) :=
    isCompact_iff_totallyBounded_isComplete.2 ⟨htb.closure, isClosed_closure.isComplete⟩
  have hmemset : ∀ n : ℕ, F n ∈ closure (Set.range F) := fun n => subset_closure ⟨n, rfl⟩
  obtain ⟨L, _, φ, hφ, htend⟩ := hcomp.tendsto_subseq hmemset
  have hnorm1 : ∀ n : ℕ, ‖F n‖ = 1 := by
    intro n
    have h1 : ‖F n‖ ^ 2 = ∫ x : ℝ, routeUHardEdgeRationalTest (a n) (p n) x ^ 2 := by
      rw [hFdef]
      exact norm_toLp_sq _
    rw [hnorm n] at h1
    nlinarith [norm_nonneg (F n)]
  refine ⟨φ, hφ, L, ?_, ?_⟩
  · have hlim := htend.norm
    have hconst : (fun k : ℕ => ‖(F ∘ φ) k‖) = fun _ : ℕ => (1 : ℝ) := by
      funext k
      exact hnorm1 (φ k)
    rw [hconst] at hlim
    exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm
  · have h2 : (F ∘ φ) = fun k : ℕ =>
        MemLp.toLp (routeUHardEdgeRationalTest (a (φ k)) (p (φ k)))
          (memLp_routeUHardEdgeRationalTest (by linarith [ha (φ k)]) (p (φ k))) := by
      funext k
      simp only [Function.comp_apply, hFdef]
    rw [← h2]
    exact htend

end RHTower

end
