import GaloisForLFunctions.«arithmetic-positivity-theory».CompactCriticalSourceWeilPositivity

/-!
# Cross-block decay of the critical prime channel

The prime channel couples two critical patterns, `b` on a dyadic block at `M` and `c` on a dyadic
block at `M'`, through
`∑_r (Λ(r)/r) ∫_{v>1} φ_r(v) B_b(v) B_c(rv) dv`.
This module proves that the coupling decays with the ratio of the two scales. The bound holds
uniformly over every finite family of dilations `r ≥ 2` and every weight family whose cosine
transforms are bounded by `A` and by `B/f²`:

`|∑_r (Λ(r)/r) ∫ φ_r B_b(v) B_c(rv) dv| ≤ K(A,B) τ(m, n) ‖b‖ ‖c‖`,

with `m = min(M, M')`, `n = max(M, M')` and `τ(m, n) = (1 + log n) √(1/n + m √(m/n))`.

The proof has four steps:

* **Harmonic reduction.** Expand both phase combinations in harmonic layers. The sum over
  dilations then becomes, for each harmonic pair `(k, l)`, the bilinear form of the combined
  kernel `∑_r (Λ(r)/r) K_{k, lr}`.
* **Cauchy–Schwarz over dilations.** The `(k, l)` form is at most `√(ρ ∑ b²) √(κ ∑ c²)`, where
  `ρ` bounds the rows and `κ` bounds the columns of the nonnegative kernel
  `∑_r (Λ(r)/r) |K_{k, lr}(n, n')|`. Unlike a separate bound for each dilation, this keeps the
  cancellation between different dilations.
* **Dilation sums.** For a fixed partner pair the dilations range over the progression `rD`.
  * Far beyond the resonance they see the `1/f²` tail.
  * Far below it they see `4B/y²`.
  * In the resonant range `y/2 < rD < 2y`, `Λ(r)/r ≤ (2D/y) log(2y/D) ≤ 6 √(D/y)`.

  So each row costs `√(lM'/(kM))` per partner when the smaller block is dilated. When the larger
  block is dilated, a row is empty of resonances unless `k > lM'/(3M)`. A column costs
  `∑_{r ≤ 6kM/M'} Λ(r)/r ≤ (1 + log(1 + 6kM/M'))²` spaced sums.
* **Harmonic summation.** The per-harmonic bound grows like `√(k√k) √l (1 + log 7k)`. Against
  the weights `1/(k² l²)` this sums to a finite mass.

The `log` in the cross-block law comes from the Mertens sum `∑ Λ(r)/r` over the resonant
dilations. The factor `m √(m/n)` counts the at most `m + 1` partners in the smaller block against
the `√(D/y)` decay of the resonant weight.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ### Bilinear harmonic reduction over a finite family of dilations -/

private theorem integrableOn_mul_bdd' {φ g : ℝ → ℝ} (hφ : IntegrableOn φ (Ioi 1)) (hg : Continuous g)
    {C : ℝ} (hC : ∀ v, |g v| ≤ C) : IntegrableOn (fun v => φ v * g v) (Ioi 1) := by
  refine (hφ.norm.const_mul C).mono' (hφ.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC v) (abs_nonneg _)

private theorem cos_sub_cos_eq_branch' (c : ℝ) (n : ℕ) (v : ℝ) :
    Real.cos (2 * Real.pi * c * (factorialShiftedFreq (n + 1) * v)) -
      Real.cos (2 * Real.pi * c * (((n + 1 : ℕ) : ℝ) * v)) =
      ∑ i : Bool, scaleBranchSign i * Real.cos (2 * Real.pi * (c * scaleBranch i n) * v) := by
  simp only [Fintype.sum_bool, scaleBranchSign, scaleBranch, if_true, Bool.false_eq_true, if_false]
  ring_nf

/-- **Bilinear harmonic kernel identity.** The weighted correlation of the harmonic layer `k` of
one pattern with the harmonic layer `l` of another, dilated by `r`, is the bilinear form of the
cross-scale kernel at frequencies `k` and `l r`. -/
theorem integral_mul_realHarmonicLayer_mul_dilate_bilinear {φ : ℝ → ℝ} (hφ : IntegrableOn φ (Ioi 1))
    (S S' : Finset ℕ) (b c : ℕ → ℝ) (k l r : ℕ) :
    ∫ v in Ioi 1, φ v * (realHarmonicLayer S b k v * realHarmonicLayer S' c l (r * v)) =
      ∑ n ∈ S, ∑ n' ∈ S', b n * c n' *
        dyadicCrossKernel (weightCosineTransform φ) k ((l * r : ℕ) : ℝ) n n' := by
  have hlayer (T : Finset ℕ) (d : ℕ → ℝ) (w : ℝ) (j : ℕ) : realHarmonicLayer T d j w =
      ∑ n ∈ T, d n * ∑ i : Bool, scaleBranchSign i *
        Real.cos (2 * Real.pi * ((j : ℝ) * scaleBranch i n) * w) := by
    unfold realHarmonicLayer
    exact Finset.sum_congr rfl fun n _ => by rw [cos_sub_cos_eq_branch']
  have hdil (n' : ℕ) (j : Bool) (v : ℝ) :
      Real.cos (2 * Real.pi * ((l : ℝ) * scaleBranch j n') * (r * v)) =
        Real.cos (2 * Real.pi * (((l * r : ℕ) : ℝ) * scaleBranch j n') * v) := by
    congr 1; push_cast; ring
  have hexp : ∀ v, φ v * (realHarmonicLayer S b k v * realHarmonicLayer S' c l (r * v)) =
      ∑ n ∈ S, ∑ n' ∈ S', b n * c n' * ∑ i : Bool, ∑ j : Bool, scaleBranchSign i * scaleBranchSign j *
        (φ v * (Real.cos (2 * Real.pi * ((k : ℝ) * scaleBranch i n) * v) *
          Real.cos (2 * Real.pi * (((l * r : ℕ) : ℝ) * scaleBranch j n') * v))) := by
    intro v
    rw [hlayer S b v k, hlayer S' c (r * v) l, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n' _ => ?_
    simp_rw [hdil, Fintype.sum_bool]
    ring
  have hint (i j : Bool) (n n' : ℕ) : IntegrableOn (fun v => φ v *
      (Real.cos (2 * Real.pi * ((k : ℝ) * scaleBranch i n) * v) *
        Real.cos (2 * Real.pi * (((l * r : ℕ) : ℝ) * scaleBranch j n') * v))) (Ioi 1) :=
    integrableOn_mul_bdd' hφ (by fun_prop) (C := 1) fun v => by
      rw [abs_mul]; exact mul_le_one₀ (Real.abs_cos_le_one _) (abs_nonneg _) (Real.abs_cos_le_one _)
  simp_rw [hexp]
  rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun n' _ =>
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hint i j n n').const_mul _).const_mul _]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_finsetSum _ fun n' _ => (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hint i j n n').const_mul _).const_mul _]
  refine Finset.sum_congr rfl fun n' _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hint i j n n').const_mul _]
  congr 1
  unfold dyadicCrossKernel
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hint i j n n').const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_mul_cos_mul_cos hφ]

/-- **Harmonic expansion of a bilinear dilation correlation.** -/
theorem hasSum_integral_weight_realPhaseCombination_dilate {φ : ℝ → ℝ} (hφ : IntegrableOn φ (Ioi 1))
    (S S' : Finset ℕ) (b c : ℕ → ℝ) (r : ℕ) :
    HasSum (fun p : ℕ × ℕ => 4 / Real.pi ^ 4 * (dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2) *
      ∑ n ∈ S, ∑ n' ∈ S', b n * c n' *
        dyadicCrossKernel (weightCosineTransform φ) p.1 ((p.2 * r : ℕ) : ℝ) n n')
      (∫ v in Ioi 1, φ v * (realPhaseCombination S b v * realPhaseCombination S' c (r * v))) := by
  set B1 := ∑ n ∈ S, |b n|
  set C1 := ∑ n ∈ S', |c n|
  have hB1 : 0 ≤ B1 := Finset.sum_nonneg fun n _ => abs_nonneg _
  have hC1 : 0 ≤ C1 := Finset.sum_nonneg fun n _ => abs_nonneg _
  have hpi4 : 0 < 4 / Real.pi ^ 4 := by positivity
  set w := dyadicHarmonicWeight
  have hw2 : Summable fun p : ℕ × ℕ => |w p.1| * |w p.2| :=
    summable_abs_dyadicHarmonicWeight.mul_of_nonneg summable_abs_dyadicHarmonicWeight
      (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
  have hhc (T : Finset ℕ) (d : ℕ → ℝ) (k : ℕ) : Continuous (realHarmonicLayer T d k) := by
    unfold realHarmonicLayer
    fun_prop
  set f : ℕ × ℕ → ℝ → ℝ := fun p v =>
    4 / Real.pi ^ 4 * (w p.1 * w p.2) *
      (φ v * (realHarmonicLayer S b p.1 v * realHarmonicLayer S' c p.2 (r * v)))
  have hprod (p : ℕ × ℕ) (v : ℝ) :
      |realHarmonicLayer S b p.1 v * realHarmonicLayer S' c p.2 (r * v)| ≤ (2 * B1) * (2 * C1) := by
    rw [abs_mul]
    exact mul_le_mul (abs_realHarmonicLayer_le S b p.1 v) (abs_realHarmonicLayer_le S' c p.2 _)
      (abs_nonneg _) (by positivity)
  have hpt (v : ℝ) : φ v * (realPhaseCombination S b v * realPhaseCombination S' c (r * v)) =
      ∑' p, f p v := by
    have h1 := realPhaseCombination_hasSum S b v
    have h2 := realPhaseCombination_hasSum S' c (r * v)
    have hs : Summable fun p : ℕ × ℕ => (w p.1 * realHarmonicLayer S b p.1 v) *
        (w p.2 * realHarmonicLayer S' c p.2 (r * v)) := by
      refine Summable.of_norm_bounded (hw2.mul_right ((2 * B1) * (2 * C1))) fun p => ?_
      rw [Real.norm_eq_abs]
      calc |w p.1 * realHarmonicLayer S b p.1 v * (w p.2 * realHarmonicLayer S' c p.2 (r * v))| =
            |w p.1| * |w p.2| * |realHarmonicLayer S b p.1 v * realHarmonicLayer S' c p.2 (r * v)| := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul]; ring
        _ ≤ |w p.1| * |w p.2| * ((2 * B1) * (2 * C1)) :=
            mul_le_mul_of_nonneg_left (hprod p v) (by positivity)
    have hm := (h1.mul h2 hs).mul_left (4 / Real.pi ^ 4 * φ v)
    have heq : (fun p => f p v) = fun i => 4 / Real.pi ^ 4 * φ v *
        (dyadicHarmonicWeight i.1 * realHarmonicLayer S b i.1 v *
          (dyadicHarmonicWeight i.2 * realHarmonicLayer S' c i.2 (r * v))) := by
      funext p
      simp only [f, w]
      ring
    rw [heq, hm.tsum_eq]
    field_simp
    ring
  have hint (p : ℕ × ℕ) : Integrable (f p) (volume.restrict (Ioi 1)) := by
    have hc : Continuous fun v => realHarmonicLayer S b p.1 v * realHarmonicLayer S' c p.2 (r * v) :=
      (hhc S b p.1).mul ((hhc S' c p.2).comp (continuous_const.mul continuous_id))
    exact (integrableOn_mul_bdd' hφ hc (hprod p)).const_mul _
  have hnorm (p : ℕ × ℕ) : ∫ v in Ioi 1, ‖f p v‖ ≤
      4 / Real.pi ^ 4 * (|w p.1| * |w p.2|) * ((2 * B1) * (2 * C1) * ∫ v in Ioi 1, |φ v|) := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_mono_on (hint p).norm ((hφ.abs.const_mul _).const_mul _) measurableSet_Ioi
      fun v _ => ?_
    simp only [f, Real.norm_eq_abs, abs_mul, abs_of_pos hpi4]
    have := hprod p v
    rw [abs_mul] at this
    have hw : 0 ≤ 4 / Real.pi ^ 4 * (|w p.1| * |w p.2|) := by positivity
    calc 4 / Real.pi ^ 4 * (|w p.1| * |w p.2|) * (|φ v| *
          (|realHarmonicLayer S b p.1 v| * |realHarmonicLayer S' c p.2 (r * v)|)) ≤
          4 / Real.pi ^ 4 * (|w p.1| * |w p.2|) * (|φ v| * ((2 * B1) * (2 * C1))) := by
          gcongr
      _ = _ := by ring
  have hsumm : Summable fun p => ∫ v in Ioi 1, ‖f p v‖ :=
    Summable.of_nonneg_of_le (fun p => integral_nonneg fun _ => norm_nonneg _) hnorm
      ((hw2.mul_left (4 / Real.pi ^ 4)).mul_right ((2 * B1) * (2 * C1) * ∫ v in Ioi 1, |φ v|))
  have hexch : ∫ v in Ioi 1, φ v * (realPhaseCombination S b v * realPhaseCombination S' c (r * v)) =
      ∑' p, ∫ v in Ioi 1, f p v := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun v _ => hpt v]
    exact (integral_tsum_of_summable_integral_norm hint hsumm).symm
  have hval (p : ℕ × ℕ) : ∫ v in Ioi 1, f p v = 4 / Real.pi ^ 4 * (w p.1 * w p.2) *
      ∑ n ∈ S, ∑ n' ∈ S', b n * c n' *
        dyadicCrossKernel (weightCosineTransform φ) p.1 ((p.2 * r : ℕ) : ℝ) n n' := by
    simp only [f]
    rw [integral_const_mul, integral_mul_realHarmonicLayer_mul_dilate_bilinear hφ]
  have hs : Summable fun p => ∫ v in Ioi 1, f p v :=
    Summable.of_norm_bounded hsumm fun p => norm_integral_le_integral_norm _
  rw [hexch]
  simp_rw [← hval]
  exact hs.hasSum

/-- **Harmonic reduction of a dilation family.** For a finite set `R` of dilations with
coefficients `a_r` and weights `φ_r`, if the `(k, l)` harmonic bilinear form of the combined
kernel `∑_r a_r K^{φ_r}_{k, lr}`, weighted by `1/(k² l²)`, is at most `μ(k, l)` with `μ` summable,
then `|∑_r a_r ∫ φ_r B_b(v) B_c(rv) dv| ≤ (4/π⁴) ∑ μ`. -/
theorem abs_sum_integral_weight_dilate_le_of_bilinear {R : Finset ℕ} (a : ℕ → ℝ) {φ : ℕ → ℝ → ℝ}
    (hφ : ∀ r ∈ R, IntegrableOn (φ r) (Ioi 1)) (S S' : Finset ℕ) (b c : ℕ → ℝ) {μ : ℕ × ℕ → ℝ}
    (hμ : Summable μ) (hμ0 : ∀ p, 0 ≤ μ p)
    (hbil : ∀ p : ℕ × ℕ, 1 ≤ p.1 → 1 ≤ p.2 → 1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2) *
      |∑ n ∈ S, ∑ n' ∈ S', b n * c n' * ∑ r ∈ R, a r *
        dyadicCrossKernel (weightCosineTransform (φ r)) p.1 ((p.2 * r : ℕ) : ℝ) n n'| ≤ μ p) :
    |∑ r ∈ R, a r * ∫ v in Ioi 1, φ r v *
        (realPhaseCombination S b v * realPhaseCombination S' c (r * v))| ≤
      4 / Real.pi ^ 4 * ∑' p, μ p := by
  set w := dyadicHarmonicWeight
  set g : ℕ × ℕ → ℝ := fun p => 4 / Real.pi ^ 4 * (w p.1 * w p.2) *
    ∑ n ∈ S, ∑ n' ∈ S', b n * c n' * ∑ r ∈ R, a r *
      dyadicCrossKernel (weightCosineTransform (φ r)) p.1 ((p.2 * r : ℕ) : ℝ) n n'
  have hsum : HasSum g (∑ r ∈ R, a r * ∫ v in Ioi 1, φ r v *
      (realPhaseCombination S b v * realPhaseCombination S' c (r * v))) := by
    have h := hasSum_sum (s := R) fun r hr =>
      (hasSum_integral_weight_realPhaseCombination_dilate (hφ r hr) S S' b c r).mul_left (a r)
    refine h.congr_fun fun p => ?_
    simp only [g, w, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun n' _ => Finset.sum_congr rfl fun r _ => by ring
  have hpi4 : 0 < 4 / Real.pi ^ 4 := by positivity
  have hbound (p : ℕ × ℕ) : |g p| ≤ 4 / Real.pi ^ 4 * μ p := by
    have hμp := hμ0 p
    rcases Nat.eq_zero_or_pos p.1 with hk | hk
    · simp only [g, w, hk, dyadicHarmonicWeight_zero, zero_mul, mul_zero, abs_zero]; positivity
    rcases Nat.eq_zero_or_pos p.2 with hl | hl
    · simp only [g, w, hl, dyadicHarmonicWeight_zero, mul_zero, zero_mul, abs_zero]; positivity
    simp only [g]
    rw [abs_mul, abs_mul, abs_of_pos hpi4, abs_mul]
    have hwk := abs_dyadicHarmonicWeight_le p.1
    have hwl := abs_dyadicHarmonicWeight_le p.2
    have hb := hbil p hk hl
    calc 4 / Real.pi ^ 4 * (|w p.1| * |w p.2|) * |_| ≤
          4 / Real.pi ^ 4 * (1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2)) * |∑ n ∈ S, ∑ n' ∈ S',
            b n * c n' * ∑ r ∈ R, a r *
              dyadicCrossKernel (weightCosineTransform (φ r)) p.1 ((p.2 * r : ℕ) : ℝ) n n'| := by
          gcongr
      _ ≤ 4 / Real.pi ^ 4 * μ p := by rw [mul_assoc]; gcongr
  have hgs : Summable fun p => 4 / Real.pi ^ 4 * μ p := hμ.mul_left _
  have habs : Summable fun p => ‖g p‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => by rw [Real.norm_eq_abs]; exact hbound p) hgs
  rw [← hsum.tsum_eq, ← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm habs).trans ?_
  refine (habs.tsum_le_tsum (fun p => by rw [Real.norm_eq_abs]; exact hbound p) hgs).trans (le_of_eq ?_)
  rw [tsum_mul_left]

/-! ### Arithmetic of the dilation weights `Λ(r)/r` -/

theorem vonMangoldt_div_nonneg (r : ℕ) : 0 ≤ (ArithmeticFunction.vonMangoldt r : ℝ) / r :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg r)

theorem vonMangoldt_div_le_log_div (r : ℕ) :
    (ArithmeticFunction.vonMangoldt r : ℝ) / r ≤ Real.log r / r :=
  div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (Nat.cast_nonneg r)

theorem vonMangoldt_div_le_one (r : ℕ) : (ArithmeticFunction.vonMangoldt r : ℝ) / r ≤ 1 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  refine (vonMangoldt_div_le_log_div r).trans ?_
  rw [div_le_one hr0]
  linarith [Real.log_le_sub_one_of_pos hr0]

/-- Tail of `∑ 1/r²`: over dilations `r ≥ X > 0` it is at most `2/X`. -/
theorem sum_one_div_sq_le_two_div (R : Finset ℕ) {X : ℝ} (hX : 0 < X) (hR : ∀ r ∈ R, X ≤ r) :
    ∑ r ∈ R, 1 / (r : ℝ) ^ 2 ≤ 2 / X := by
  set k := ⌈X⌉₊ - 1
  have hc : 0 < ⌈X⌉₊ := Nat.ceil_pos.mpr hX
  have hsub : R ⊆ Finset.Ioo k (R.sup id + 1) := fun r hr => by
    have h1 : ⌈X⌉₊ ≤ r := Nat.ceil_le.mpr (hR r hr)
    have h2 : r ≤ R.sup id := Finset.le_sup (f := id) hr
    simp only [Finset.mem_Ioo]; omega
  have hk : ((k : ℕ) : ℝ) + 1 = ⌈X⌉₊ := by
    have : k + 1 = ⌈X⌉₊ := by omega
    exact_mod_cast this
  calc ∑ r ∈ R, 1 / (r : ℝ) ^ 2 ≤ ∑ r ∈ Finset.Ioo k (R.sup id + 1), ((r : ℝ) ^ 2)⁻¹ := by
        simp_rw [one_div]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ 2 / ((k : ℝ) + 1) := sum_Ioo_inv_sq_le k _
    _ ≤ 2 / X := by rw [hk]; exact div_le_div_of_nonneg_left (by norm_num) hX (Nat.le_ceil X)

/-- Counting: at most `X` positive dilations lie below `X`. -/
theorem card_le_of_le (R : Finset ℕ) {X : ℝ} (hX : 0 ≤ X) (hR : ∀ r ∈ R, 1 ≤ r ∧ (r : ℝ) ≤ X) :
    (R.card : ℝ) ≤ X := by
  have hsub : R ⊆ Finset.Icc 1 ⌊X⌋₊ := fun r hr => by
    simp only [Finset.mem_Icc]; exact ⟨(hR r hr).1, Nat.le_floor (hR r hr).2⟩
  have h := Finset.card_le_card hsub
  simp only [Nat.card_Icc, add_tsub_cancel_right] at h
  exact (Nat.cast_le.mpr h).trans (Nat.floor_le hX)

/-- Mertens-type partial sum: `∑_{1 ≤ r ≤ X} Λ(r)/r ≤ (1 + log X)²` for `X ≥ 1`. -/
theorem sum_vonMangoldt_div_le (R : Finset ℕ) {X : ℝ} (hX : 1 ≤ X)
    (hR : ∀ r ∈ R, 1 ≤ r ∧ (r : ℝ) ≤ X) :
    ∑ r ∈ R, (ArithmeticFunction.vonMangoldt r : ℝ) / r ≤ (1 + Real.log X) ^ 2 := by
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have hsub : R ⊆ Finset.Icc 1 ⌊X⌋₊ := fun r hr => by
    simp only [Finset.mem_Icc]; exact ⟨(hR r hr).1, Nat.le_floor (hR r hr).2⟩
  have hharm : ∑ r ∈ Finset.Icc 1 ⌊X⌋₊, 1 / (r : ℝ) ≤ 1 + Real.log X := by
    have h := harmonic_le_one_add_log ⌊X⌋₊
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    simp_rw [one_div]
    have hl : Real.log (⌊X⌋₊ : ℝ) ≤ Real.log X :=
      Real.log_le_log (by exact_mod_cast Nat.floor_pos.mpr hX) (Nat.floor_le (by linarith))
    linarith
  calc ∑ r ∈ R, (ArithmeticFunction.vonMangoldt r : ℝ) / r ≤ ∑ r ∈ R, Real.log X * (1 / (r : ℝ)) := by
        refine Finset.sum_le_sum fun r hr => (vonMangoldt_div_le_log_div r).trans ?_
        have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (hR r hr).1
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_right (Real.log_le_log (by linarith) (hR r hr).2) (by positivity)
    _ = Real.log X * ∑ r ∈ R, 1 / (r : ℝ) := by rw [Finset.mul_sum]
    _ ≤ Real.log X * ∑ r ∈ Finset.Icc 1 ⌊X⌋₊, 1 / (r : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub
          fun _ _ _ => by positivity) hlog
    _ ≤ Real.log X * (1 + Real.log X) := mul_le_mul_of_nonneg_left hharm hlog
    _ ≤ (1 + Real.log X) ^ 2 := by nlinarith

/-! ### Spaced sums and the dilation sum -/

/-- **Spaced summation for a family.** If every `F_m` is bounded by `A` and by `B/f²`, and the
points `y_m` are `s`-spaced along the indices, then `∑_m |F_m(x - y_m)| ≤ A + (4B/s²)(π²/3)`. -/
theorem sum_abs_le_of_spaced_family {F : ℕ → ℝ → ℝ} {A B : ℝ} (hA : ∀ m f, |F m f| ≤ A)
    (hB : ∀ m f, f ≠ 0 → |F m f| ≤ B / f ^ 2) (hB0 : 0 ≤ B) (T : Finset ℕ) (y : ℕ → ℝ) (x : ℝ)
    {s : ℝ} (hs : 0 < s) (hsp : ∀ m ∈ T, ∀ m' ∈ T, s * |(m : ℝ) - m'| ≤ |y m - y m'|) :
    ∑ m ∈ T, |F m (x - y m)| ≤ A + 4 * B / s ^ 2 * (Real.pi ^ 2 / 3) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 0)
  rcases T.eq_empty_or_nonempty with rfl | hT
  · simp only [Finset.sum_empty]; positivity
  obtain ⟨m₀, hm₀, hmin⟩ := T.exists_min_image (fun m => |x - y m|) hT
  rw [← Finset.add_sum_erase T _ hm₀]
  refine add_le_add (hA _ _) ?_
  have hterm : ∀ m ∈ T.erase m₀, |F m (x - y m)| ≤ 4 * B / s ^ 2 * (1 / ((m : ℝ) - m₀) ^ 2) := by
    intro m hm
    have hm' := Finset.mem_of_mem_erase hm
    have hne : (m : ℝ) ≠ m₀ := by exact_mod_cast Finset.ne_of_mem_erase hm
    have hd : 0 < |(m : ℝ) - m₀| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have hsp' := hsp m hm' m₀ hm₀
    have htri : |y m - y m₀| ≤ 2 * |x - y m| := by
      have := abs_sub_le (y m) x (y m₀)
      rw [abs_sub_comm (y m) x, abs_sub_comm x (y m₀)] at this
      have h2 := hmin m hm'
      rw [abs_sub_comm (y m₀) x] at this
      linarith
    have hlow : s / 2 * |(m : ℝ) - m₀| ≤ |x - y m| := by linarith
    have hpos : 0 < |x - y m| := lt_of_lt_of_le (by positivity) hlow
    have hxne : x - y m ≠ 0 := abs_pos.mp hpos
    refine (hB m _ hxne).trans ?_
    rw [← sq_abs (x - y m)]
    have hsq : (s / 2 * |(m : ℝ) - m₀|) ^ 2 ≤ |x - y m| ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlow 2
    rw [div_le_iff₀ (by positivity)]
    have e : 4 * B / s ^ 2 * (1 / ((m : ℝ) - m₀) ^ 2) * |x - y m| ^ 2 =
        B * (|x - y m| ^ 2 / (s / 2 * |(m : ℝ) - m₀|) ^ 2) := by
      rw [mul_pow]
      field_simp
      rw [sq_abs]
      ring
    rw [e]
    have h1 : 1 ≤ |x - y m| ^ 2 / (s / 2 * |(m : ℝ) - m₀|) ^ 2 := by
      rw [one_le_div (by positivity)]; exact hsq
    nlinarith
  calc ∑ m ∈ T.erase m₀, |F m (x - y m)| ≤
        ∑ m ∈ T.erase m₀, 4 * B / s ^ 2 * (1 / ((m : ℝ) - m₀) ^ 2) := Finset.sum_le_sum hterm
    _ = 4 * B / s ^ 2 * ∑ m ∈ T.erase m₀, 1 / ((m : ℝ) - m₀) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 4 * B / s ^ 2 * (Real.pi ^ 2 / 3) :=
        mul_le_mul_of_nonneg_left (sum_erase_inv_sq_le T m₀) (by positivity)

private theorem abs_le_of_far {F : ℝ → ℝ} {B : ℝ} (hB : ∀ f, f ≠ 0 → |F f| ≤ B / f ^ 2)
    (hB0 : 0 ≤ B) {f d : ℝ} (hd : 0 < d) (hf : d ≤ |f|) : |F f| ≤ B / d ^ 2 := by
  have hf0 : f ≠ 0 := abs_pos.mp (lt_of_lt_of_le hd hf)
  refine (hB f hf0).trans ?_
  rw [← sq_abs f]
  exact div_le_div_of_nonneg_left hB0 (by positivity) (pow_le_pow_left₀ hd.le hf 2)

/-- `(2D/y) log(2y/D) ≤ 6 √(D/y)`. -/
private theorem mul_log_le_sqrt {y D : ℝ} (hy : 0 < y) (hD : 0 < D) :
    2 * D / y * Real.log (2 * y / D) ≤ 6 * Real.sqrt (D / y) := by
  have ht : 0 < 2 * y / D := by positivity
  have hlog := Real.log_le_rpow_div ht.le (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at hlog
  have hs : Real.sqrt (2 * y / D) = Real.sqrt 2 / Real.sqrt (D / y) := by
    rw [show 2 * y / D = 2 / (D / y) by field_simp, Real.sqrt_div' 2 (by positivity : (0 : ℝ) ≤ D / y)]
  have hq : 0 < Real.sqrt (D / y) := Real.sqrt_pos.mpr (by positivity)
  have hsq : Real.sqrt (D / y) ^ 2 = D / y := Real.sq_sqrt (by positivity)
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  calc 2 * D / y * Real.log (2 * y / D) ≤ 2 * D / y * (Real.sqrt (2 * y / D) / (1 / 2)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 4 * Real.sqrt 2 * Real.sqrt (D / y) := by
        rw [hs, show 2 * D / y = 2 * Real.sqrt (D / y) ^ 2 by rw [hsq]; ring]
        field_simp
        ring
    _ ≤ 6 * Real.sqrt (D / y) := by nlinarith

/-- **Dilation sum.** For `y, D > 0` and dilations `r ≥ 2`, the prime-weighted sum of a kernel
family along the progression `r D` satisfies two bounds:
* `≤ 9B/(yD) + 6 √(D/y) (A + 14B/D²)`;
* `≤ 5B/D²` plus, only when `D < y`, the resonant part `2B/(yD) + 6 √(D/y) (A + 14B/D²)`.
Dilations far beyond `y/D` see the `1/f²` tail, dilations far below see `4B/y²`, and in the
resonant range `y/2 < rD < 2y` the weight is at most `(2D/y) log(2y/D)` against one spaced sum. -/
theorem dilationSum_le {F : ℕ → ℝ → ℝ} {A B : ℝ} (hA : ∀ m f, |F m f| ≤ A)
    (hB : ∀ m f, f ≠ 0 → |F m f| ≤ B / f ^ 2) (hB0 : 0 ≤ B) (R : Finset ℕ) (hR : ∀ r ∈ R, 2 ≤ r)
    {y D : ℝ} (hy : 0 < y) (hD : 0 < D) :
    ∑ r ∈ R, (ArithmeticFunction.vonMangoldt r : ℝ) / r * (|F r (y - r * D)| + |F r (y + r * D)|) ≤
        9 * B / (y * D) + 6 * Real.sqrt (D / y) * (A + 14 * B / D ^ 2) ∧
    ∑ r ∈ R, (ArithmeticFunction.vonMangoldt r : ℝ) / r * (|F r (y - r * D)| + |F r (y + r * D)|) ≤
        5 * B / D ^ 2 + if D < y then 2 * B / (y * D) + 6 * Real.sqrt (D / y) * (A + 14 * B / D ^ 2)
          else 0 := by
  set a : ℕ → ℝ := fun r => (ArithmeticFunction.vonMangoldt r : ℝ) / r
  have ha0 (r : ℕ) : 0 ≤ a r := vonMangoldt_div_nonneg r
  have ha1 (r : ℕ) : a r ≤ 1 := vonMangoldt_div_le_one r
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 0)
  have hr0 : ∀ r ∈ R, (2 : ℝ) ≤ r := fun r hr => by exact_mod_cast hR r hr
  have hW : 0 ≤ 6 * Real.sqrt (D / y) * (A + 14 * B / D ^ 2) := by positivity
  -- the three ranges of the main term
  set R1 := R.filter fun r : ℕ => 2 * y ≤ r * D with hR1def
  set R23 := R.filter fun r : ℕ => ¬ 2 * y ≤ r * D with hR23def
  set R2 := R23.filter fun r : ℕ => r * D ≤ y / 2
  set R3 := R23.filter fun r : ℕ => ¬ r * D ≤ y / 2
  have hsplit : ∑ r ∈ R, a r * |F r (y - r * D)| =
      ∑ r ∈ R1, a r * |F r (y - r * D)| + (∑ r ∈ R2, a r * |F r (y - r * D)| +
        ∑ r ∈ R3, a r * |F r (y - r * D)|) := by
    rw [Finset.sum_filter_add_sum_filter_not R23, Finset.sum_filter_add_sum_filter_not R]
  -- range I: the `1/f²` tail
  have hI1 : ∑ r ∈ R1, a r * |F r (y - r * D)| ≤ 4 * B / D ^ 2 * ∑ r ∈ R1, 1 / (r : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r hr => ?_
    have hr' := (Finset.mem_filter.mp hr)
    have hrD : 0 < (r : ℝ) * D := by have := hr0 r hr'.1; positivity
    have hfar : (r : ℝ) * D / 2 ≤ |y - r * D| := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hr'.2])]; linarith [hr'.2]
    have := abs_le_of_far (hB r) hB0 (by positivity) hfar
    calc a r * |F r (y - r * D)| ≤ 1 * (B / ((r : ℝ) * D / 2) ^ 2) :=
          mul_le_mul (ha1 r) this (abs_nonneg _) zero_le_one
      _ = 4 * B / D ^ 2 * (1 / (r : ℝ) ^ 2) := by field_simp; ring
  have hR1a : ∑ r ∈ R1, 1 / (r : ℝ) ^ 2 ≤ 1 := by
    have := sum_one_div_sq_le_two_div R1 (X := 2) (by norm_num) fun r hr =>
      hr0 r (Finset.mem_filter.mp hr).1
    linarith
  have hR1b : ∑ r ∈ R1, 1 / (r : ℝ) ^ 2 ≤ D / y := by
    have := sum_one_div_sq_le_two_div R1 (X := 2 * y / D) (by positivity) fun r hr => by
      rw [div_le_iff₀ hD]; exact (Finset.mem_filter.mp hr).2
    rwa [show 2 / (2 * y / D) = D / y by field_simp] at this
  have hIa : ∑ r ∈ R1, a r * |F r (y - r * D)| ≤ 4 * B / D ^ 2 :=
    hI1.trans (by
      have : 0 ≤ 4 * B / D ^ 2 := by positivity
      nlinarith)
  have hIb : ∑ r ∈ R1, a r * |F r (y - r * D)| ≤ 4 * B / (y * D) :=
    hI1.trans (by
      have : 0 ≤ 4 * B / D ^ 2 := by positivity
      calc 4 * B / D ^ 2 * ∑ r ∈ R1, 1 / (r : ℝ) ^ 2 ≤ 4 * B / D ^ 2 * (D / y) :=
            mul_le_mul_of_nonneg_left hR1b this
        _ = 4 * B / (y * D) := by field_simp)
  -- range II: dilations far below the resonance
  have hR2 : ∀ r ∈ R2, (r : ℝ) * D ≤ y / 2 := fun r hr => (Finset.mem_filter.mp hr).2
  have hR2R : ∀ r ∈ R2, r ∈ R := fun r hr =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
  have hII : ∑ r ∈ R2, a r * |F r (y - r * D)| ≤ 2 * B / (y * D) := by
    have hcard : (R2.card : ℝ) ≤ y / (2 * D) := card_le_of_le R2 (by positivity) fun r hr => by
      refine ⟨by have := hR r (hR2R r hr); omega, ?_⟩
      rw [le_div_iff₀ (by positivity)]; linarith [hR2 r hr]
    calc ∑ r ∈ R2, a r * |F r (y - r * D)| ≤ ∑ _r ∈ R2, 4 * B / y ^ 2 := by
          refine Finset.sum_le_sum fun r hr => ?_
          have hfar : y / 2 ≤ |y - r * D| := by
            rw [abs_of_nonneg (by linarith [hR2 r hr])]; linarith [hR2 r hr]
          have := abs_le_of_far (hB r) hB0 (by positivity) hfar
          calc a r * |F r (y - r * D)| ≤ 1 * (B / (y / 2) ^ 2) :=
                mul_le_mul (ha1 r) this (abs_nonneg _) zero_le_one
            _ = 4 * B / y ^ 2 := by field_simp; ring
      _ = R2.card * (4 * B / y ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ y / (2 * D) * (4 * B / y ^ 2) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 * B / (y * D) := by field_simp; ring
  have hII0 : R2.Nonempty → D < y := fun ⟨r, hr⟩ => by
    have h2 := hr0 r (hR2R r hr)
    have := hR2 r hr
    nlinarith
  -- range III: the resonant dilations
  have hR3R : ∀ r ∈ R3, r ∈ R := fun r hr =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
  have hR3 : ∀ r ∈ R3, y / 2 < (r : ℝ) * D ∧ (r : ℝ) * D < 2 * y := fun r hr =>
    ⟨lt_of_not_ge (Finset.mem_filter.mp hr).2,
      lt_of_not_ge (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2⟩
  have hIII : ∑ r ∈ R3, a r * |F r (y - r * D)| ≤ 6 * Real.sqrt (D / y) * (A + 14 * B / D ^ 2) := by
    have hsp := sum_abs_le_of_spaced_family hA hB hB0 R3 (fun r => (r : ℝ) * D) y hD
      fun m _ m' _ => by rw [← sub_mul, abs_mul, abs_of_pos hD, mul_comm]
    have hw : ∀ r ∈ R3, a r ≤ 2 * D / y * Real.log (2 * y / D) := by
      intro r hr
      have h2 := hr0 r (hR3R r hr)
      have hr' : (0 : ℝ) < r := by linarith
      obtain ⟨h1, h3⟩ := hR3 r hr
      refine (vonMangoldt_div_le_log_div r).trans ?_
      have hlog : Real.log r ≤ Real.log (2 * y / D) :=
        Real.log_le_log hr' (by rw [le_div_iff₀ hD]; linarith)
      have hlog0 : 0 ≤ Real.log (2 * y / D) := hlog.trans' (Real.log_nonneg (by linarith))
      have hinv : 1 / (r : ℝ) ≤ 2 * D / y := by
        rw [div_le_div_iff₀ hr' hy]; linarith
      calc Real.log r / r = Real.log r * (1 / (r : ℝ)) := by ring
        _ ≤ Real.log (2 * y / D) * (2 * D / y) :=
            mul_le_mul hlog hinv (by positivity) hlog0
        _ = 2 * D / y * Real.log (2 * y / D) := by ring
    rcases R3.eq_empty_or_nonempty with h | h
    · rw [h, Finset.sum_empty]; exact hW
    obtain ⟨r₀, hr₀⟩ := h
    have hlog0 : 0 ≤ Real.log (2 * y / D) := by
      have h2 := hr0 r₀ (hR3R r₀ hr₀)
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ hD]; nlinarith [(hR3 r₀ hr₀).2]
    calc ∑ r ∈ R3, a r * |F r (y - r * D)| ≤ ∑ r ∈ R3, 2 * D / y * Real.log (2 * y / D) *
          |F r (y - r * D)| :=
          Finset.sum_le_sum fun r hr => mul_le_mul_of_nonneg_right (hw r hr) (abs_nonneg _)
      _ = 2 * D / y * Real.log (2 * y / D) * ∑ r ∈ R3, |F r (y - r * D)| := by rw [Finset.mul_sum]
      _ ≤ 6 * Real.sqrt (D / y) * (A + 4 * B / D ^ 2 * (Real.pi ^ 2 / 3)) :=
          mul_le_mul (mul_log_le_sqrt hy hD) hsp (Finset.sum_nonneg fun _ _ => abs_nonneg _)
            (by positivity)
      _ ≤ 6 * Real.sqrt (D / y) * (A + 14 * B / D ^ 2) := by
          have hpi := Real.pi_lt_d2
          have : 4 * B / D ^ 2 * (Real.pi ^ 2 / 3) ≤ 14 * B / D ^ 2 := by
            rw [show 4 * B / D ^ 2 * (Real.pi ^ 2 / 3) = B / D ^ 2 * (4 * Real.pi ^ 2 / 3) by ring,
              show 14 * B / D ^ 2 = B / D ^ 2 * 14 by ring]
            exact mul_le_mul_of_nonneg_left (by nlinarith [Real.pi_pos]) (by positivity)
          gcongr
  have hIII0 : R3.Nonempty → D < y := fun ⟨r, hr⟩ => by
    have h2 := hr0 r (hR3R r hr)
    have := (hR3 r hr).2
    nlinarith
  -- the sum-frequency terms
  have hsumA : ∑ r ∈ R, a r * |F r (y + r * D)| ≤ B / D ^ 2 := by
    calc ∑ r ∈ R, a r * |F r (y + r * D)| ≤ ∑ r ∈ R, B / D ^ 2 * (1 / (r : ℝ) ^ 2) := by
          refine Finset.sum_le_sum fun r hr => ?_
          have h2 := hr0 r hr
          have hfar : (r : ℝ) * D ≤ |y + r * D| := by
            rw [abs_of_pos (by positivity)]; linarith
          have := abs_le_of_far (hB r) hB0 (by positivity) hfar
          calc a r * |F r (y + r * D)| ≤ 1 * (B / ((r : ℝ) * D) ^ 2) :=
                mul_le_mul (ha1 r) this (abs_nonneg _) zero_le_one
            _ = B / D ^ 2 * (1 / (r : ℝ) ^ 2) := by field_simp
      _ = B / D ^ 2 * ∑ r ∈ R, 1 / (r : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ B / D ^ 2 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := sum_one_div_sq_le_two_div R (X := 2) (by norm_num) hr0
          linarith
      _ = B / D ^ 2 := mul_one _
  have hsumB : ∑ r ∈ R, a r * |F r (y + r * D)| ≤ 3 * B / (y * D) := by
    have hs := Finset.sum_filter_add_sum_filter_not R (fun r : ℕ => 2 * y ≤ r * D)
      (fun r => a r * |F r (y + r * D)|)
    rw [← hR1def, ← hR23def] at hs
    rw [← hs]
    have h1 : ∑ r ∈ R1, a r * |F r (y + r * D)| ≤ B / (y * D) := by
      calc ∑ r ∈ R1, a r * |F r (y + r * D)| ≤ ∑ r ∈ R1, B / D ^ 2 * (1 / (r : ℝ) ^ 2) := by
            refine Finset.sum_le_sum fun r hr => ?_
            have h2 := hr0 r (Finset.mem_filter.mp hr).1
            have hfar : (r : ℝ) * D ≤ |y + r * D| := by
              rw [abs_of_pos (by positivity)]; linarith
            have := abs_le_of_far (hB r) hB0 (by positivity) hfar
            calc a r * |F r (y + r * D)| ≤ 1 * (B / ((r : ℝ) * D) ^ 2) :=
                  mul_le_mul (ha1 r) this (abs_nonneg _) zero_le_one
              _ = B / D ^ 2 * (1 / (r : ℝ) ^ 2) := by field_simp
        _ = B / D ^ 2 * ∑ r ∈ R1, 1 / (r : ℝ) ^ 2 := by rw [Finset.mul_sum]
        _ ≤ B / D ^ 2 * (D / y) := mul_le_mul_of_nonneg_left hR1b (by positivity)
        _ = B / (y * D) := by field_simp
    have h2 : ∑ r ∈ R23, a r * |F r (y + r * D)| ≤ 2 * B / (y * D) := by
      have hcard : (R23.card : ℝ) ≤ 2 * y / D := card_le_of_le R23 (by positivity) fun r hr => by
        have hr' := Finset.mem_filter.mp hr
        refine ⟨by have := hR r hr'.1; omega, ?_⟩
        rw [le_div_iff₀ hD]; linarith [lt_of_not_ge hr'.2]
      calc ∑ r ∈ R23, a r * |F r (y + r * D)| ≤ ∑ _r ∈ R23, B / y ^ 2 := by
            refine Finset.sum_le_sum fun r hr => ?_
            have h2 := hr0 r (Finset.mem_filter.mp hr).1
            have hfar : y ≤ |y + r * D| := by
              rw [abs_of_pos (by positivity)]; nlinarith
            have := abs_le_of_far (hB r) hB0 hy hfar
            calc a r * |F r (y + r * D)| ≤ 1 * (B / y ^ 2) :=
                  mul_le_mul (ha1 r) this (abs_nonneg _) zero_le_one
              _ = B / y ^ 2 := one_mul _
        _ = R23.card * (B / y ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 2 * y / D * (B / y ^ 2) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 2 * B / (y * D) := by field_simp
    have e : 3 * B / (y * D) = B / (y * D) + 2 * B / (y * D) := by ring
    linarith
  have hexp : ∑ r ∈ R, a r * (|F r (y - r * D)| + |F r (y + r * D)|) =
      ∑ r ∈ R, a r * |F r (y - r * D)| + ∑ r ∈ R, a r * |F r (y + r * D)| := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun r _ => by ring
  have hII' : 0 ≤ ∑ r ∈ R2, a r * |F r (y - r * D)| :=
    Finset.sum_nonneg fun r _ => mul_nonneg (ha0 r) (abs_nonneg _)
  have hIII' : 0 ≤ ∑ r ∈ R3, a r * |F r (y - r * D)| :=
    Finset.sum_nonneg fun r _ => mul_nonneg (ha0 r) (abs_nonneg _)
  have e9 : 9 * B / (y * D) = 4 * B / (y * D) + 2 * B / (y * D) + 3 * B / (y * D) := by ring
  have e5 : 5 * B / D ^ 2 = 4 * B / D ^ 2 + B / D ^ 2 := by ring
  refine ⟨?_, ?_⟩
  · show ∑ r ∈ R, a r * (|F r (y - r * D)| + |F r (y + r * D)|) ≤ _
    rw [hexp, hsplit]
    linarith
  · show ∑ r ∈ R, a r * (|F r (y - r * D)| + |F r (y + r * D)|) ≤ _
    rw [hexp, hsplit]
    split_ifs with hDy
    · linarith
    · have e2 : R2 = ∅ := Finset.not_nonempty_iff_eq_empty.mp fun h => hDy (hII0 h)
      have e3 : R3 = ∅ := Finset.not_nonempty_iff_eq_empty.mp fun h => hDy (hIII0 h)
      rw [e2, e3, Finset.sum_empty]
      linarith

/-! ### Row and column bounds of the cross-block dilation kernel -/

theorem weightCosineTransform_neg (φ : ℝ → ℝ) (f : ℝ) :
    weightCosineTransform φ (-f) = weightCosineTransform φ f := by
  unfold weightCosineTransform
  congr 1; funext v
  rw [show 2 * Real.pi * -f * v = -(2 * Real.pi * f * v) by ring, Real.cos_neg]

private theorem abs_dyadicCrossKernel_le' (F : ℝ → ℝ) (p q : ℝ) (n n' : ℕ) :
    |dyadicCrossKernel F p q n n'| ≤ ∑ i : Bool, ∑ j : Bool,
      (|F (p * scaleBranch i n - q * scaleBranch j n')| +
        |F (p * scaleBranch i n + q * scaleBranch j n')|) / 2 := by
  unfold dyadicCrossKernel
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hs : |scaleBranchSign i * scaleBranchSign j| = 1 := by
    unfold scaleBranchSign; cases i <;> cases j <;> norm_num
  rw [abs_mul, hs, one_mul, abs_div, abs_two]
  exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)

/-- **Cauchy–Schwarz for a nonnegative kernel.** If the rows of `G ≥ 0` sum to at most `ρ` and
the columns to at most `κ`, then `∑ |x_n| |y_m| G_{nm} ≤ √(ρ ∑ x²) √(κ ∑ y²)`. -/
theorem sum_abs_mul_abs_mul_le_sqrt {S S' : Finset ℕ} (x y : ℕ → ℝ) (G : ℕ → ℕ → ℝ)
    (hG : ∀ n m, 0 ≤ G n m) {ρ κ : ℝ} (hρ : 0 ≤ ρ)
    (hrow : ∀ n ∈ S, ∑ m ∈ S', G n m ≤ ρ) (hcol : ∀ m ∈ S', ∑ n ∈ S, G n m ≤ κ) :
    ∑ n ∈ S, ∑ m ∈ S', |x n| * |y m| * G n m ≤
      Real.sqrt (ρ * ∑ n ∈ S, x n ^ 2) * Real.sqrt (κ * ∑ m ∈ S', y m ^ 2) := by
  set T := ∑ n ∈ S, ∑ m ∈ S', |x n| * |y m| * G n m
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (S ×ˢ S') (fun p => |x p.1| * Real.sqrt (G p.1 p.2))
    (fun p => |y p.2| * Real.sqrt (G p.1 p.2))
  rw [Finset.sum_product, Finset.sum_product, Finset.sum_product] at hcs
  have e1 : ∑ n ∈ S, ∑ m ∈ S', |x n| * Real.sqrt (G n m) * (|y m| * Real.sqrt (G n m)) = T := by
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    have := Real.mul_self_sqrt (hG n m)
    calc _ = |x n| * |y m| * (Real.sqrt (G n m) * Real.sqrt (G n m)) := by ring
      _ = _ := by rw [this]
  have e2 : ∑ n ∈ S, ∑ m ∈ S', (|x n| * Real.sqrt (G n m)) ^ 2 ≤ ρ * ∑ n ∈ S, x n ^ 2 := by
    calc _ = ∑ n ∈ S, x n ^ 2 * ∑ m ∈ S', G n m := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [mul_pow, sq_abs, Real.sq_sqrt (hG n m)]
      _ ≤ ∑ n ∈ S, x n ^ 2 * ρ :=
          Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hrow n hn) (sq_nonneg _)
      _ = ρ * ∑ n ∈ S, x n ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
  have e3 : ∑ n ∈ S, ∑ m ∈ S', (|y m| * Real.sqrt (G n m)) ^ 2 ≤ κ * ∑ m ∈ S', y m ^ 2 := by
    rw [Finset.sum_comm]
    calc _ = ∑ m ∈ S', y m ^ 2 * ∑ n ∈ S, G n m := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [mul_pow, sq_abs, Real.sq_sqrt (hG n m)]
      _ ≤ ∑ m ∈ S', y m ^ 2 * κ :=
          Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hcol m hm) (sq_nonneg _)
      _ = κ * ∑ m ∈ S', y m ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
  have h0 : 0 ≤ ∑ n ∈ S, ∑ m ∈ S', (|y m| * Real.sqrt (G n m)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq : T ^ 2 ≤ (ρ * ∑ n ∈ S, x n ^ 2) * (κ * ∑ m ∈ S', y m ^ 2) := by
    rw [← e1]
    exact hcs.trans (mul_le_mul e2 e3 h0 (mul_nonneg hρ (Finset.sum_nonneg fun _ _ => sq_nonneg _)))
  rw [← Real.sqrt_mul (mul_nonneg hρ (Finset.sum_nonneg fun _ _ => sq_nonneg _))]
  exact (le_abs_self T).trans (Real.abs_le_sqrt hsq)

/-- The dilation sum `∑_r (Λ(r)/r) (|F_r(y - rD)| + |F_r(y + rD)|)`. -/
def primeDilationSum (F : ℕ → ℝ → ℝ) (R : Finset ℕ) (y D : ℝ) : ℝ :=
  ∑ r ∈ R, (ArithmeticFunction.vonMangoldt r : ℝ) / r * (|F r (y - r * D)| + |F r (y + r * D)|)

/-- The prime-weighted dilation kernel is dominated branch by branch by dilation sums. -/
theorem sum_vonMangoldt_mul_abs_dyadicCrossKernel_le (F : ℕ → ℝ → ℝ) (R : Finset ℕ) (k l : ℕ)
    (n n' : ℕ) :
    ∑ r ∈ R, (ArithmeticFunction.vonMangoldt r : ℝ) / r *
        |dyadicCrossKernel (F r) k ((l * r : ℕ) : ℝ) n n'| ≤
      ∑ i : Bool, ∑ j : Bool,
        primeDilationSum F R (k * scaleBranch i n) (l * scaleBranch j n') / 2 := by
  unfold primeDilationSum
  have hq (r : ℕ) (j : Bool) : ((l * r : ℕ) : ℝ) * scaleBranch j n' = r * (l * scaleBranch j n') := by
    push_cast; ring
  calc ∑ r ∈ R, (ArithmeticFunction.vonMangoldt r : ℝ) / r *
        |dyadicCrossKernel (F r) k ((l * r : ℕ) : ℝ) n n'| ≤
      ∑ r ∈ R, (ArithmeticFunction.vonMangoldt r : ℝ) / r * ∑ i : Bool, ∑ j : Bool,
        (|F r (k * scaleBranch i n - r * (l * scaleBranch j n'))| +
          |F r (k * scaleBranch i n + r * (l * scaleBranch j n'))|) / 2 := by
        refine Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left ?_ (vonMangoldt_div_nonneg r)
        have h := abs_dyadicCrossKernel_le' (F r) k ((l * r : ℕ) : ℝ) n n'
        simp only [hq] at h
        exact h
    _ = _ := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun r _ => by ring

/-- **Row bound.** If `β` dominates every dilation sum with `y ∈ [kM, 3kM]` and `D ∈ [lM', 3lM']`,
the prime-weighted kernel rows over a block at `M'` are at most `2(M' + 1) β`. -/
theorem sum_row_dilationKernel_le (F : ℕ → ℝ → ℝ) (R : Finset ℕ) {S S' : Finset ℕ} {M M' : ℕ}
    (hM : 1 ≤ M) (hM' : 1 ≤ M') (hS : DyadicScaleBlock S M) (hS' : DyadicScaleBlock S' M') (k l : ℕ)
    {β : ℝ} (hβnn : 0 ≤ β) (hβ : ∀ y D : ℝ, k * M ≤ y → y ≤ 3 * (k * M) → l * M' ≤ D →
      D ≤ 3 * (l * M') → primeDilationSum F R y D ≤ β) {n : ℕ} (hn : n ∈ S) :
    ∑ n' ∈ S', ∑ r ∈ R, (ArithmeticFunction.vonMangoldt r : ℝ) / r *
        |dyadicCrossKernel (F r) k ((l * r : ℕ) : ℝ) n n'| ≤ 2 * (M' + 1) * β := by
  have hβ0 : ∀ i j : Bool, ∀ n' ∈ S', primeDilationSum F R (k * scaleBranch i n) (l * scaleBranch j n') ≤ β :=
    fun i j n' hn' => by
      have hx := scaleBranch_mem_block hM hS i hn
      have hy := scaleBranch_mem_block hM' hS' j hn'
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
      exact hβ _ _ (mul_le_mul_of_nonneg_left hx.1 hk0) (by nlinarith [hx.2])
        (mul_le_mul_of_nonneg_left hy.1 hl0) (by nlinarith [hy.2])
  have hcard : (S'.card : ℝ) ≤ M' + 1 := by exact_mod_cast hS'.card_le
  calc _ ≤ ∑ n' ∈ S', ∑ i : Bool, ∑ j : Bool,
        primeDilationSum F R (k * scaleBranch i n) (l * scaleBranch j n') / 2 :=
        Finset.sum_le_sum fun n' _ => sum_vonMangoldt_mul_abs_dyadicCrossKernel_le F R k l n n'
    _ ≤ ∑ _n' ∈ S', 2 * β := by
        refine Finset.sum_le_sum fun n' hn' => ?_
        simp only [Fintype.sum_bool]
        linarith [hβ0 true true n' hn', hβ0 true false n' hn', hβ0 false true n' hn',
          hβ0 false false n' hn']
    _ = S'.card * (2 * β) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M' + 1) * (2 * β) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 * (M' + 1) * β := by ring

/-- **Column dilation sum.** Over a block at `M`, with branch frequencies `y_n = k θ_i(n)`, the dilation
sums at a fixed `D ≥ 1` add up to at most `2(A + 16B)(1 + log(1 + 6kM/D))² + 4B`: dilations with
`rD < 6kM` cost one spaced sum each against `∑ Λ(r)/r`, the others see only the `1/f²` tail. -/
theorem sum_dilationSum_branch_le {F : ℕ → ℝ → ℝ} {A B : ℝ} (hA : ∀ m f, |F m f| ≤ A)
    (hB : ∀ m f, f ≠ 0 → |F m f| ≤ B / f ^ 2) (hB0 : 0 ≤ B) (hev : ∀ m f, F m (-f) = F m f)
    (R : Finset ℕ) (hR : ∀ r ∈ R, 2 ≤ r) {S : Finset ℕ} {M : ℕ} (hM : 1 ≤ M)
    (hS : DyadicScaleBlock S M) {k : ℕ} (hk : 1 ≤ k) (i : Bool) {D : ℝ} (hD : 1 ≤ D) :
    ∑ n ∈ S, primeDilationSum F R (k * scaleBranch i n) D ≤
      2 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / D)) ^ 2 + 4 * B := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 0)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hD0 : 0 < D := by linarith
  set y : ℕ → ℝ := fun n => k * scaleBranch i n
  have hy (n : ℕ) (hn : n ∈ S) : k * M ≤ y n ∧ y n ≤ 3 * (k * M) := by
    have hx := scaleBranch_mem_block hM hS i hn
    exact ⟨mul_le_mul_of_nonneg_left hx.1 (by linarith), by nlinarith [hx.2]⟩
  have hsp : ∀ m ∈ S, ∀ m' ∈ S, 11 * k / 12 * |(m : ℝ) - m'| ≤ |y m - y m'| := by
    intro m _ m' _
    have := scaleBranch_spacing i m m'
    simp only [y]
    rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ k)]
    nlinarith [abs_nonneg ((m : ℝ) - m')]
  have hspC : 4 * B / (11 * k / 12) ^ 2 * (Real.pi ^ 2 / 3) ≤ 16 * B := by
    have hpi := Real.pi_lt_d2
    have hk2 : (11 / 12 : ℝ) ^ 2 ≤ (11 * k / 12) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : 4 * B * (Real.pi ^ 2 / 3) ≤ 16 * B * (11 / 12) ^ 2 := by
      have : Real.pi ^ 2 ≤ 3.15 ^ 2 := pow_le_pow_left₀ Real.pi_pos.le (by linarith) 2
      nlinarith
    nlinarith
  -- per dilation, the spaced bound
  have hpair (r : ℕ) : ∑ n ∈ S, (|F r (y n - r * D)| + |F r (y n + r * D)|) ≤ 2 * (A + 16 * B) := by
    have h1 := sum_abs_le_of_spaced_family (fun _ => hA r) (fun _ => hB r) hB0 S y (r * D)
      (by positivity) hsp
    have h2 := sum_abs_le_of_spaced_family (fun _ => hA r) (fun _ => hB r) hB0 S y (-(r * D))
      (by positivity) hsp
    have e1 : ∀ n, |F r (y n - r * D)| = |F r (r * D - y n)| := fun n => by
      rw [← hev r (r * D - y n), neg_sub]
    have e2 : ∀ n, |F r (y n + r * D)| = |F r (-(r * D) - y n)| := fun n => by
      rw [← hev r (-(r * D) - y n)]; ring_nf
    rw [Finset.sum_add_distrib]
    simp_rw [e1, e2]
    linarith
  -- far dilations
  have hfar (r : ℕ) (hr : 6 * (k * M) ≤ r * D) :
      ∑ n ∈ S, (|F r (y n - r * D)| + |F r (y n + r * D)|) ≤ (M + 1) * (5 * B / D ^ 2 * (1 / (r : ℝ) ^ 2)) := by
    have hrD : 0 < (r : ℝ) * D := lt_of_lt_of_le (by positivity) hr
    have hcard : (S.card : ℝ) ≤ M + 1 := by exact_mod_cast hS.card_le
    calc ∑ n ∈ S, (|F r (y n - r * D)| + |F r (y n + r * D)|) ≤ ∑ _n ∈ S, 5 * B / D ^ 2 * (1 / (r : ℝ) ^ 2) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have h := hy n hn
          have f1 : (r : ℝ) * D / 2 ≤ |y n - r * D| := by
            rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
          have f2 : (r : ℝ) * D ≤ |y n + r * D| := by
            rw [abs_of_nonneg (by linarith)]; linarith
          have g1 := abs_le_of_far (hB r) hB0 (by positivity) f1
          have g2 := abs_le_of_far (hB r) hB0 hrD f2
          calc _ ≤ B / ((r : ℝ) * D / 2) ^ 2 + B / ((r : ℝ) * D) ^ 2 := add_le_add g1 g2
            _ = 5 * B / D ^ 2 * (1 / (r : ℝ) ^ 2) := by field_simp; ring
      _ = S.card * (5 * B / D ^ 2 * (1 / (r : ℝ) ^ 2)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (M + 1) * (5 * B / D ^ 2 * (1 / (r : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
  unfold primeDilationSum
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_filter_add_sum_filter_not R (fun r : ℕ => (r : ℝ) * D < 6 * (k * M))]
  have hnear : ∑ r ∈ R.filter (fun r : ℕ => (r : ℝ) * D < 6 * (k * M)), (ArithmeticFunction.vonMangoldt r : ℝ) / r *
      ∑ n ∈ S, (|F r (y n - r * D)| + |F r (y n + r * D)|) ≤
      2 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / D)) ^ 2 := by
    calc _ ≤ ∑ r ∈ R.filter (fun r : ℕ => (r : ℝ) * D < 6 * (k * M)), (ArithmeticFunction.vonMangoldt r : ℝ) / r *
          (2 * (A + 16 * B)) :=
          Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (hpair r) (vonMangoldt_div_nonneg r)
      _ = 2 * (A + 16 * B) * ∑ r ∈ R.filter (fun r : ℕ => (r : ℝ) * D < 6 * (k * M)),
          (ArithmeticFunction.vonMangoldt r : ℝ) / r := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
      _ ≤ 2 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / D)) ^ 2 := by
          refine mul_le_mul_of_nonneg_left (sum_vonMangoldt_div_le _ (by
            have : 0 ≤ 6 * (k * M) / D := by positivity
            linarith) fun r hr => ?_) (by positivity)
          have hr' := Finset.mem_filter.mp hr
          refine ⟨by have := hR r hr'.1; omega, ?_⟩
          have : (r : ℝ) ≤ 6 * (k * M) / D := by rw [le_div_iff₀ hD0]; linarith [hr'.2]
          linarith
  have hfar' : ∑ r ∈ R.filter (fun r : ℕ => ¬ (r : ℝ) * D < 6 * (k * M)), (ArithmeticFunction.vonMangoldt r : ℝ) / r *
      ∑ n ∈ S, (|F r (y n - r * D)| + |F r (y n + r * D)|) ≤ 4 * B := by
    have hsq := sum_one_div_sq_le_two_div (R.filter fun r : ℕ => ¬ (r : ℝ) * D < 6 * (k * M))
      (X := 6 * (k * M) / D) (by positivity) fun r hr => by
        rw [div_le_iff₀ hD0]; exact not_lt.mp (Finset.mem_filter.mp hr).2
    calc _ ≤ ∑ r ∈ R.filter (fun r : ℕ => ¬ (r : ℝ) * D < 6 * (k * M)),
          (M + 1) * (5 * B / D ^ 2 * (1 / (r : ℝ) ^ 2)) := by
          refine Finset.sum_le_sum fun r hr => ?_
          have hfr := hfar r (not_lt.mp (Finset.mem_filter.mp hr).2)
          have hs0 : 0 ≤ ∑ n ∈ S, (|F r (y n - r * D)| + |F r (y n + r * D)|) :=
            Finset.sum_nonneg fun _ _ => by positivity
          calc _ ≤ 1 * ∑ n ∈ S, (|F r (y n - r * D)| + |F r (y n + r * D)|) :=
                mul_le_mul_of_nonneg_right (vonMangoldt_div_le_one r) hs0
            _ ≤ _ := by rw [one_mul]; exact hfr
      _ = (M + 1) * (5 * B / D ^ 2) * ∑ r ∈ R.filter (fun r : ℕ => ¬ (r : ℝ) * D < 6 * (k * M)), 1 / (r : ℝ) ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
      _ ≤ (M + 1) * (5 * B / D ^ 2) * (2 / (6 * (k * M) / D)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (M + 1) / M * (5 * B / (3 * k * D)) := by field_simp; ring
      _ ≤ 2 * (5 * B / 3) := by
          have h1 : (M + 1 : ℝ) / M ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
          have h2 : 5 * B / (3 * k * D) ≤ 5 * B / 3 := by
            apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
            nlinarith
          exact mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ ≤ 4 * B := by linarith
  linarith

/-- **Column bound** of the prime-weighted dilation kernel over a block at `M`, for partners on a
block at `M'`. -/
theorem sum_col_dilationKernel_le {φ : ℕ → ℝ → ℝ} {A B : ℝ}
    (hA : ∀ m f, |weightCosineTransform (φ m) f| ≤ A)
    (hB : ∀ m f, f ≠ 0 → |weightCosineTransform (φ m) f| ≤ B / f ^ 2) (hB0 : 0 ≤ B)
    (R : Finset ℕ) (hR : ∀ r ∈ R, 2 ≤ r) {S S' : Finset ℕ} {M M' : ℕ} (hM : 1 ≤ M) (hM' : 1 ≤ M')
    (hS : DyadicScaleBlock S M) (hS' : DyadicScaleBlock S' M') {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    {n' : ℕ} (hn' : n' ∈ S') :
    ∑ n ∈ S, ∑ r ∈ R, (ArithmeticFunction.vonMangoldt r : ℝ) / r *
        |dyadicCrossKernel (weightCosineTransform (φ r)) k ((l * r : ℕ) : ℝ) n n'| ≤
      12 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / M')) ^ 2 := by
  set F : ℕ → ℝ → ℝ := fun r => weightCosineTransform (φ r)
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 0)
  have hM'1 : (1 : ℝ) ≤ M' := by exact_mod_cast hM'
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hL : 1 ≤ 1 + Real.log (1 + 6 * (k * M) / M') :=
    le_add_of_nonneg_right (Real.log_nonneg (le_add_of_nonneg_right (by positivity)))
  have hbr (i j : Bool) : ∑ n ∈ S, primeDilationSum F R (k * scaleBranch i n) (l * scaleBranch j n') ≤
      2 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / M')) ^ 2 + 4 * B := by
    have hy := scaleBranch_mem_block hM' hS' j hn'
    have hD1 : (M' : ℝ) ≤ l * scaleBranch j n' := by nlinarith [hy.1]
    refine (sum_dilationSum_branch_le hA hB hB0 (fun m f => weightCosineTransform_neg _ _) R hR hM hS
      hk i (by linarith)).trans ?_
    have hθ : (0 : ℝ) < l * scaleBranch j n' := by linarith
    have hq0 : 0 ≤ 6 * (k * M) / (l * scaleBranch j n') := by positivity
    have hq1 : 6 * (k * M) / (l * scaleBranch j n') ≤ 6 * (k * M) / M' :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hD1
    have hlog : Real.log (1 + 6 * (k * M) / (l * scaleBranch j n')) ≤ Real.log (1 + 6 * (k * M) / M') :=
      Real.log_le_log (by linarith) (by linarith)
    have h0 : 0 ≤ 1 + Real.log (1 + 6 * (k * M) / (l * scaleBranch j n')) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + 6 * (k * M) / (l * scaleBranch j n') by linarith)
      linarith
    have hsq := pow_le_pow_left₀ h0 (by linarith : 1 + Real.log (1 + 6 * (k * M) / (l * scaleBranch j n')) ≤
      1 + Real.log (1 + 6 * (k * M) / M')) 2
    have hW : 0 ≤ 2 * (A + 16 * B) := by positivity
    nlinarith
  calc _ ≤ ∑ n ∈ S, ∑ i : Bool, ∑ j : Bool,
        primeDilationSum F R (k * scaleBranch i n) (l * scaleBranch j n') / 2 :=
        Finset.sum_le_sum fun n _ => sum_vonMangoldt_mul_abs_dyadicCrossKernel_le F R k l n n'
    _ = ∑ i : Bool, ∑ j : Bool, (∑ n ∈ S, primeDilationSum F R (k * scaleBranch i n) (l * scaleBranch j n')) / 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_div]
    _ ≤ ∑ _i : Bool, ∑ _j : Bool,
        (2 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / M')) ^ 2 + 4 * B) / 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          div_le_div_of_nonneg_right (hbr i j) (by norm_num)
    _ = 4 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / M')) ^ 2 + 8 * B := by
        simp only [Fintype.sum_bool]; ring
    _ ≤ 12 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / M')) ^ 2 := by
        have hsq : 1 ≤ (1 + Real.log (1 + 6 * (k * M) / M')) ^ 2 := one_le_pow₀ hL
        nlinarith

/-! ### Per-harmonic cross-block bounds -/

/-- Cross-block decay `τ(m, n) = (1 + log n) √(1/n + m √(m/n))` between a block at `m` and a block
at `n`. -/
def crossBlockDecay (m n : ℕ) : ℝ := (1 + Real.log n) * Real.sqrt (1 / n + m * Real.sqrt (m / n))

theorem crossBlockDecay_nonneg (m n : ℕ) : 0 ≤ crossBlockDecay m n := by
  unfold crossBlockDecay
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  positivity

/-- Harmonic factor `√(k √k) √l (1 + log 7k)` of the cross-block bound. -/
def crossBlockHarmonicFactor (k l : ℕ) : ℝ :=
  Real.sqrt (k * Real.sqrt k) * Real.sqrt l * (1 + Real.log (7 * k))

theorem crossBlockHarmonicFactor_nonneg {k : ℕ} (hk : 1 ≤ k) (l : ℕ) :
    0 ≤ crossBlockHarmonicFactor k l := by
  have : 0 ≤ Real.log (7 * k) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith)
  unfold crossBlockHarmonicFactor; positivity

private theorem crossBlockHarmonicFactor_sq {k : ℕ} (hk : 1 ≤ k) (l : ℕ) :
    crossBlockHarmonicFactor k l ^ 2 = k * Real.sqrt k * l * (1 + Real.log (7 * k)) ^ 2 := by
  unfold crossBlockHarmonicFactor
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]

private theorem crossBlockDecay_sq (m n : ℕ) :
    crossBlockDecay m n ^ 2 = (1 + Real.log n) ^ 2 * (1 / n + m * Real.sqrt (m / n)) := by
  unfold crossBlockDecay
  rw [mul_pow, Real.sq_sqrt (by positivity)]

private theorem sqrt_mul_sqrt_le_of_mul_le {ρ κ X Y T : ℝ} (hρ : 0 ≤ ρ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hT : 0 ≤ T) (h : ρ * κ ≤ T ^ 2) :
    Real.sqrt (ρ * X) * Real.sqrt (κ * Y) ≤ T * Real.sqrt X * Real.sqrt Y := by
  calc Real.sqrt (ρ * X) * Real.sqrt (κ * Y) = Real.sqrt (ρ * X * (κ * Y)) :=
        (Real.sqrt_mul (mul_nonneg hρ hX) _).symm
    _ = Real.sqrt (ρ * κ * (X * Y)) := by congr 1; ring
    _ ≤ Real.sqrt (T ^ 2 * (X * Y)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h (mul_nonneg hX hY))
    _ = T * Real.sqrt X * Real.sqrt Y := by
        rw [Real.sqrt_mul (sq_nonneg T), Real.sqrt_sq hT, Real.sqrt_mul hX, mul_assoc]

private theorem abs_bilinear_le_kernel (S S' R : Finset ℕ) (b c : ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ) :
    |∑ n ∈ S, ∑ n' ∈ S', b n * c n' * ∑ r ∈ R, (ArithmeticFunction.vonMangoldt r : ℝ) / r * K r n n'| ≤
      ∑ n ∈ S, ∑ n' ∈ S', |b n| * |c n'| *
        ∑ r ∈ R, (ArithmeticFunction.vonMangoldt r : ℝ) / r * |K r n n'| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n' _ => ?_)
  rw [abs_mul, abs_mul]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun r _ => ?_)) (by positivity)
  rw [abs_mul, abs_of_nonneg (vonMangoldt_div_nonneg r)]

/-- **Per-harmonic cross-block bound from a dilation-sum majorant.** If `β ≥ 0` dominates the
dilation sums on the block ranges and `2(M' + 1) β · 12(A + 16B) L² ≤ T²`, with
`L = 1 + log(1 + 6kM/M')`, the `(k, l)` harmonic cross form is at most `T ‖b‖ ‖c‖`. -/
theorem abs_bilinear_crossBlock_le_of_bounds {φ : ℕ → ℝ → ℝ} {A B : ℝ}
    (hA : ∀ m f, |weightCosineTransform (φ m) f| ≤ A)
    (hB : ∀ m f, f ≠ 0 → |weightCosineTransform (φ m) f| ≤ B / f ^ 2) (hB0 : 0 ≤ B)
    (R : Finset ℕ) (hR : ∀ r ∈ R, 2 ≤ r) {S S' : Finset ℕ} {M M' : ℕ} (hM : 1 ≤ M) (hM' : 1 ≤ M')
    (hS : DyadicScaleBlock S M) (hS' : DyadicScaleBlock S' M') (b c : ℕ → ℝ) {k l : ℕ} (hk : 1 ≤ k)
    (hl : 1 ≤ l) {β T : ℝ} (hβ0 : 0 ≤ β)
    (hβ : ∀ y D : ℝ, k * M ≤ y → y ≤ 3 * (k * M) → l * M' ≤ D → D ≤ 3 * (l * M') →
      primeDilationSum (fun r => weightCosineTransform (φ r)) R y D ≤ β) (hT : 0 ≤ T)
    (hprod : 2 * (M' + 1 : ℝ) * β * (12 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / M')) ^ 2) ≤
      T ^ 2) :
    |∑ n ∈ S, ∑ n' ∈ S', b n * c n' * ∑ r ∈ R, (ArithmeticFunction.vonMangoldt r : ℝ) / r *
        dyadicCrossKernel (weightCosineTransform (φ r)) k ((l * r : ℕ) : ℝ) n n'| ≤
      T * Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n ∈ S', c n ^ 2) := by
  have hrow := fun n hn => sum_row_dilationKernel_le (fun r => weightCosineTransform (φ r)) R hM hM'
    hS hS' k l hβ0 hβ (n := n) hn
  have hcol := fun n' hn' => sum_col_dilationKernel_le hA hB hB0 R hR hM hM' hS hS' hk hl (n' := n') hn'
  have hG : ∀ n n', 0 ≤ ∑ r ∈ R, (ArithmeticFunction.vonMangoldt r : ℝ) / r *
      |dyadicCrossKernel (weightCosineTransform (φ r)) k ((l * r : ℕ) : ℝ) n n'| := fun n n' =>
    Finset.sum_nonneg fun r _ => mul_nonneg (vonMangoldt_div_nonneg r) (abs_nonneg _)
  have hcs := sum_abs_mul_abs_mul_le_sqrt b c _ hG (by positivity) hrow hcol
  exact (abs_bilinear_le_kernel S S' R b c _).trans (hcs.trans (sqrt_mul_sqrt_le_of_mul_le
    (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) hT hprod))

private theorem one_add_log_mul_le {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    1 + Real.log (x * y) ≤ (1 + Real.log x) * (1 + Real.log y) := by
  rw [Real.log_mul (by linarith) (by linarith)]
  have := Real.log_nonneg hx
  have := Real.log_nonneg hy
  nlinarith

private theorem one_le_mul_sqrt {k : ℕ} (hk : 1 ≤ k) : 1 ≤ (k : ℝ) * Real.sqrt k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have : 1 ≤ Real.sqrt k := by rw [Real.one_le_sqrt]; exact hk1
  nlinarith

private theorem log_bracket_le {k M M' : ℕ} (hk : 1 ≤ k) (hM : 1 ≤ M) (hM' : 1 ≤ M') :
    0 ≤ 1 + Real.log (1 + 6 * (k * M) / M') ∧
      1 + Real.log (1 + 6 * (k * M) / M') ≤ (1 + Real.log (7 * k)) * (1 + Real.log M) ∧
      (M ≤ M' → 1 + Real.log (1 + 6 * (k * M) / M') ≤ 1 + Real.log (7 * k)) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM'1 : (1 : ℝ) ≤ M' := by exact_mod_cast hM'
  have hq : 0 ≤ 6 * (k * M) / (M' : ℝ) := by positivity
  have hpos : (0 : ℝ) < 1 + 6 * (k * M) / M' := by linarith
  refine ⟨by have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + 6 * (k * M) / M' by linarith); linarith,
    ?_, fun hMM => ?_⟩
  · have h1 : (1 : ℝ) + 6 * (k * M) / M' ≤ 7 * k * M := by
      have : 6 * (k * M) / (M' : ℝ) ≤ 6 * (k * M) := div_le_self (by positivity) hM'1
      nlinarith
    calc 1 + Real.log (1 + 6 * (k * M) / M') ≤ 1 + Real.log (7 * k * M) := by
          have := Real.log_le_log hpos h1; linarith
      _ ≤ _ := one_add_log_mul_le (by linarith) hM1
  · have hMM' : (M : ℝ) ≤ M' := by exact_mod_cast hMM
    have h1 : (1 : ℝ) + 6 * (k * M) / M' ≤ 7 * k := by
      have : 6 * (k * M) / (M' : ℝ) ≤ 6 * k := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      linarith
    have := Real.log_le_log hpos h1
    linarith

/-- **Per-harmonic bound, downward order.** The smaller block (at `M' ≤ M`) is dilated: the
resonant dilations `r ≈ kM/(lM')` cost `√(lM'/(kM))` per partner, against `M' + 1` partners. -/
theorem abs_bilinear_crossBlock_down_le {φ : ℕ → ℝ → ℝ} {A B : ℝ}
    (hA : ∀ m f, |weightCosineTransform (φ m) f| ≤ A)
    (hB : ∀ m f, f ≠ 0 → |weightCosineTransform (φ m) f| ≤ B / f ^ 2) (hB0 : 0 ≤ B)
    (R : Finset ℕ) (hR : ∀ r ∈ R, 2 ≤ r) {S S' : Finset ℕ} {M M' : ℕ} (hM' : 1 ≤ M') (hMM : M' ≤ M)
    (hS : DyadicScaleBlock S M) (hS' : DyadicScaleBlock S' M') (b c : ℕ → ℝ) {k l : ℕ} (hk : 1 ≤ k)
    (hl : 1 ≤ l) :
    |∑ n ∈ S, ∑ n' ∈ S', b n * c n' * ∑ r ∈ R, (ArithmeticFunction.vonMangoldt r : ℝ) / r *
        dyadicCrossKernel (weightCosineTransform (φ r)) k ((l * r : ℕ) : ℝ) n n'| ≤
      39 * (A + 16 * B) * crossBlockHarmonicFactor k l * crossBlockDecay M' M *
        Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n ∈ S', c n ^ 2) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 0)
  have hW : 0 ≤ A + 16 * B := by positivity
  have hM : 1 ≤ M := hM'.trans hMM
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM'1 : (1 : ℝ) ≤ M' := by exact_mod_cast hM'
  have hβ0 : 0 ≤ 9 * B / (k * M * (l * M')) + 6 * Real.sqrt (3 * (l * M') / (k * M)) * (A + 14 * B) := by
    positivity
  refine abs_bilinear_crossBlock_le_of_bounds hA hB hB0 R hR hM hM' hS hS' b c hk hl hβ0 ?_
    (by have := crossBlockHarmonicFactor_nonneg hk l; have := crossBlockDecay_nonneg M' M; positivity) ?_
  · intro y D hy1 _ hD1 hD2
    have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy1
    have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD1
    have hD1' : 1 ≤ D := le_trans (by nlinarith) hD1
    refine (dilationSum_le hA hB hB0 R hR hy0 hD0).1.trans (add_le_add ?_ ?_)
    · exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul hy1 hD1 (by positivity) hy0.le)
    · refine mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)) ?_
        (by positivity) (by positivity)
      · rw [div_le_div_iff₀ hy0 (by positivity)]; nlinarith
      · have : 14 * B / D ^ 2 ≤ 14 * B := div_le_self (by positivity) (one_le_pow₀ hD1')
        linarith
  · -- product bound
    obtain ⟨hL0, hL, -⟩ := log_bracket_le (k := k) hk hM hM'
    set Q := 1 / (M : ℝ) + M' * Real.sqrt (M' / M)
    have hQ : 0 ≤ Q := by positivity
    have hsl : 1 ≤ Real.sqrt l := by rw [Real.one_le_sqrt]; exact hl1
    have h1 : 9 * B / (k * M * (l * M')) ≤ 9 * (A + 16 * B) / (M * M') := by
      apply div_le_div₀ (by positivity) (by linarith) (by positivity)
      calc (M : ℝ) * M' = 1 * M * (1 * M') := by ring
        _ ≤ k * M * (l * M') := by gcongr
    have h2 : Real.sqrt (3 * (l * M') / (k * M)) ≤ 2 * Real.sqrt l * Real.sqrt (M' / M) := by
      have e : 2 * Real.sqrt l * Real.sqrt (M' / M) = Real.sqrt (4 * l * (M' / M)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
          show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [e]
      refine Real.sqrt_le_sqrt ?_
      rw [div_le_iff₀ (by positivity)]
      have : (0 : ℝ) ≤ l * M' := by positivity
      field_simp
      nlinarith
    have hβ' : 9 * B / (k * M * (l * M')) + 6 * Real.sqrt (3 * (l * M') / (k * M)) * (A + 14 * B) ≤
        9 * (A + 16 * B) / (M * M') + 12 * (A + 16 * B) * Real.sqrt l * Real.sqrt (M' / M) := by
      have : 6 * Real.sqrt (3 * (l * M') / (k * M)) * (A + 14 * B) ≤
          6 * (2 * Real.sqrt l * Real.sqrt (M' / M)) * (A + 16 * B) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      linarith
    have hρ : 2 * (M' + 1 : ℝ) * (9 * B / (k * M * (l * M')) +
        6 * Real.sqrt (3 * (l * M') / (k * M)) * (A + 14 * B)) ≤ 48 * (A + 16 * B) * Real.sqrt l * Q := by
      calc _ ≤ 2 * (2 * M') * (9 * (A + 16 * B) / (M * M') +
            12 * (A + 16 * B) * Real.sqrt l * Real.sqrt (M' / M)) :=
            mul_le_mul (by linarith) hβ' hβ0 (by positivity)
        _ = 36 * (A + 16 * B) * (1 / M) + 48 * (A + 16 * B) * Real.sqrt l * (M' * Real.sqrt (M' / M)) := by
            field_simp; ring
        _ ≤ 48 * (A + 16 * B) * Real.sqrt l * (1 / M) +
            48 * (A + 16 * B) * Real.sqrt l * (M' * Real.sqrt (M' / M)) := by
            have : 36 * (A + 16 * B) ≤ 48 * (A + 16 * B) * Real.sqrt l := by nlinarith
            have := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ 1 / M)
            linarith
        _ = 48 * (A + 16 * B) * Real.sqrt l * Q := by ring
    have hκ : 12 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / M')) ^ 2 ≤
        12 * (A + 16 * B) * ((1 + Real.log (7 * k)) * (1 + Real.log M)) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hL 2) (by positivity)
    have hsK : Real.sqrt l ≤ k * Real.sqrt k * l := by
      have : Real.sqrt l ≤ l := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
      nlinarith [one_le_mul_sqrt hk]
    have hT2 : (39 * (A + 16 * B) * crossBlockHarmonicFactor k l * crossBlockDecay M' M) ^ 2 =
        1521 * (A + 16 * B) ^ 2 * (k * Real.sqrt k * l) *
          ((1 + Real.log (7 * k)) * (1 + Real.log M)) ^ 2 * Q := by
      rw [mul_pow, mul_pow, mul_pow, crossBlockHarmonicFactor_sq hk, crossBlockDecay_sq]
      ring
    rw [hT2]
    set P := ((1 + Real.log (7 * k)) * (1 + Real.log M)) ^ 2
    have hP : 0 ≤ P := sq_nonneg _
    calc _ ≤ (48 * (A + 16 * B) * Real.sqrt l * Q) * (12 * (A + 16 * B) * P) :=
          mul_le_mul hρ hκ (by positivity) (by positivity)
      _ = (576 * Real.sqrt l) * ((A + 16 * B) ^ 2 * P * Q) := by ring
      _ ≤ (1521 * (k * Real.sqrt k * l)) * ((A + 16 * B) ^ 2 * P * Q) := by
          have hX : (0 : ℝ) ≤ k * Real.sqrt k * l := by positivity
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring

/-- **Per-harmonic bound, upward order.** The larger block (at `M' ≥ M`) is dilated: every dilation
`r ≥ 2` already overshoots unless `k > lM'/(3M)`, and the excess harmonics are paid by
`(3kM/(lM'))^{3/2}`. -/
theorem abs_bilinear_crossBlock_up_le {φ : ℕ → ℝ → ℝ} {A B : ℝ}
    (hA : ∀ m f, |weightCosineTransform (φ m) f| ≤ A)
    (hB : ∀ m f, f ≠ 0 → |weightCosineTransform (φ m) f| ≤ B / f ^ 2) (hB0 : 0 ≤ B)
    (R : Finset ℕ) (hR : ∀ r ∈ R, 2 ≤ r) {S S' : Finset ℕ} {M M' : ℕ} (hM : 1 ≤ M) (hMM : M ≤ M')
    (hS : DyadicScaleBlock S M) (hS' : DyadicScaleBlock S' M') (b c : ℕ → ℝ) {k l : ℕ} (hk : 1 ≤ k)
    (hl : 1 ≤ l) :
    |∑ n ∈ S, ∑ n' ∈ S', b n * c n' * ∑ r ∈ R, (ArithmeticFunction.vonMangoldt r : ℝ) / r *
        dyadicCrossKernel (weightCosineTransform (φ r)) k ((l * r : ℕ) : ℝ) n n'| ≤
      39 * (A + 16 * B) * crossBlockHarmonicFactor k l * crossBlockDecay M M' *
        Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n ∈ S', c n ^ 2) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 0)
  have hW : 0 ≤ A + 16 * B := by positivity
  have hM' : 1 ≤ M' := hM.trans hMM
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM'1 : (1 : ℝ) ≤ M' := by exact_mod_cast hM'
  have hMM' : (M : ℝ) ≤ M' := by exact_mod_cast hMM
  set t := 3 * (k * M) / (l * M' : ℝ)
  have ht0 : 0 ≤ t := by positivity
  have hβ0 : 0 ≤ 5 * B / (l * M') ^ 2 + t * Real.sqrt t * (6 * A + 86 * B) := by positivity
  refine abs_bilinear_crossBlock_le_of_bounds hA hB hB0 R hR hM hM' hS hS' b c hk hl hβ0 ?_
    (by have := crossBlockHarmonicFactor_nonneg hk l; have := crossBlockDecay_nonneg M M'; positivity) ?_
  · intro y D hy1 hy2 hD1 hD2
    have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy1
    have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD1
    have hD1' : 1 ≤ D := le_trans (by nlinarith) hD1
    have hy1' : 1 ≤ y := le_trans (by nlinarith) hy1
    refine (dilationSum_le hA hB hB0 R hR hy0 hD0).2.trans (add_le_add ?_ ?_)
    · exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hD1 2)
    · split_ifs with hDy
      · have hyD : 1 ≤ y / D := by rw [le_div_iff₀ hD0]; linarith
        have htD : y / D ≤ t := by
          simp only [t]
          rw [div_le_div_iff₀ hD0 (by positivity)]
          nlinarith
        have hsq : 1 ≤ Real.sqrt (y / D) := by rw [Real.one_le_sqrt]; exact hyD
        have hone : 1 ≤ t * Real.sqrt t := by
          have h1 : 1 ≤ t := hyD.trans htD
          have h2 : 1 ≤ Real.sqrt t := by rw [Real.one_le_sqrt]; exact h1
          nlinarith
        have h1 : 2 * B / (y * D) ≤ 2 * B :=
          div_le_self (by positivity) (by nlinarith)
        have h2 : Real.sqrt (D / y) ≤ 1 := by
          rw [Real.sqrt_le_one]; rw [div_le_one hy0]; linarith
        have h3 : 14 * B / D ^ 2 ≤ 14 * B := div_le_self (by positivity) (one_le_pow₀ hD1')
        have h4 : 6 * Real.sqrt (D / y) * (A + 14 * B / D ^ 2) ≤ 6 * (A + 14 * B) := by
          have : 0 ≤ A + 14 * B / D ^ 2 := by positivity
          nlinarith [Real.sqrt_nonneg (D / y)]
        calc 2 * B / (y * D) + 6 * Real.sqrt (D / y) * (A + 14 * B / D ^ 2) ≤ 1 * (6 * A + 86 * B) := by
              linarith
          _ ≤ t * Real.sqrt t * (6 * A + 86 * B) :=
              mul_le_mul_of_nonneg_right hone (by positivity)
      · positivity
  · obtain ⟨hL0, -, hL⟩ := log_bracket_le (k := k) hk hM hM'
    have hL := hL hMM
    set Q := 1 / (M' : ℝ) + M * Real.sqrt (M / M')
    have hQ : 0 ≤ Q := by positivity
    have hksk := one_le_mul_sqrt hk
    set u := 3 * (k * M) / (M' : ℝ)
    have htu : t ≤ u := by
      simp only [t, u]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    have hu : u * Real.sqrt u = 3 * Real.sqrt 3 * (k * Real.sqrt k) * (M / M' * Real.sqrt (M / M')) := by
      have e : u = 3 * k * (M / M') := by simp only [u]; ring
      rw [e, Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
      ring
    have hs3 : Real.sqrt 3 ≤ 1.733 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have htsq : t * Real.sqrt t ≤ u * Real.sqrt u :=
      mul_le_mul htu (Real.sqrt_le_sqrt htu) (Real.sqrt_nonneg _) (ht0.trans htu)
    have hρ : 2 * (M' + 1 : ℝ) * (5 * B / (l * M') ^ 2 + t * Real.sqrt t * (6 * A + 86 * B)) ≤
        125 * (A + 16 * B) * (k * Real.sqrt k) * Q := by
      have h1 : 5 * B / (l * M') ^ 2 ≤ 5 * (A + 16 * B) / (M' : ℝ) ^ 2 := by
        apply div_le_div₀ (by positivity) (by linarith) (by positivity)
        exact pow_le_pow_left₀ (by positivity) (by nlinarith) 2
      have h2 : t * Real.sqrt t * (6 * A + 86 * B) ≤ u * Real.sqrt u * (6 * (A + 16 * B)) :=
        mul_le_mul htsq (by linarith) (by positivity) (by positivity)
      have hM'2 : (M' + 1 : ℝ) ≤ 2 * M' := by linarith
      have hMM2 : (M' : ℝ) * (M / M' * Real.sqrt (M / M')) = M * Real.sqrt (M / M') := by
        field_simp
      calc _ ≤ 2 * (2 * M') * (5 * (A + 16 * B) / (M' : ℝ) ^ 2 + u * Real.sqrt u * (6 * (A + 16 * B))) :=
            mul_le_mul (by linarith) (add_le_add h1 h2) hβ0 (by positivity)
        _ = 20 * (A + 16 * B) * (1 / M') +
            72 * Real.sqrt 3 * (A + 16 * B) * (k * Real.sqrt k) * (M' * (M / M' * Real.sqrt (M / M'))) := by
            rw [hu]; field_simp; ring
        _ = 20 * (A + 16 * B) * (1 / M') +
            72 * Real.sqrt 3 * (A + 16 * B) * (k * Real.sqrt k) * (M * Real.sqrt (M / M')) := by
            rw [hMM2]
        _ ≤ 125 * (A + 16 * B) * (k * Real.sqrt k) * (1 / M') +
            125 * (A + 16 * B) * (k * Real.sqrt k) * (M * Real.sqrt (M / M')) := by
            have e1 : 20 * (A + 16 * B) ≤ 125 * (A + 16 * B) * (k * Real.sqrt k) :=
              calc 20 * (A + 16 * B) ≤ 125 * (A + 16 * B) * 1 := by linarith
                _ ≤ 125 * (A + 16 * B) * (k * Real.sqrt k) :=
                    mul_le_mul_of_nonneg_left hksk (by positivity)
            have e2 : 72 * Real.sqrt 3 * (A + 16 * B) * (k * Real.sqrt k) ≤
                125 * (A + 16 * B) * (k * Real.sqrt k) := by
              have hX : 0 ≤ (A + 16 * B) * (k * Real.sqrt k) := by positivity
              calc 72 * Real.sqrt 3 * (A + 16 * B) * (k * Real.sqrt k) =
                    (72 * Real.sqrt 3) * ((A + 16 * B) * (k * Real.sqrt k)) := by ring
                _ ≤ 125 * ((A + 16 * B) * (k * Real.sqrt k)) :=
                    mul_le_mul_of_nonneg_right (by linarith) hX
                _ = 125 * (A + 16 * B) * (k * Real.sqrt k) := by ring
            have := mul_le_mul_of_nonneg_right e1 (by positivity : (0 : ℝ) ≤ 1 / M')
            have := mul_le_mul_of_nonneg_right e2 (by positivity : (0 : ℝ) ≤ M * Real.sqrt (M / M'))
            linarith
        _ = 125 * (A + 16 * B) * (k * Real.sqrt k) * Q := by ring
    have hκ : 12 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / M')) ^ 2 ≤
        12 * (A + 16 * B) * (1 + Real.log (7 * k)) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hL 2) (by positivity)
    have hT2 : (39 * (A + 16 * B) * crossBlockHarmonicFactor k l * crossBlockDecay M M') ^ 2 =
        1521 * (A + 16 * B) ^ 2 * (k * Real.sqrt k) * l * (1 + Real.log (7 * k)) ^ 2 *
          (1 + Real.log M') ^ 2 * Q := by
      rw [mul_pow, mul_pow, mul_pow, crossBlockHarmonicFactor_sq hk, crossBlockDecay_sq]
      ring
    rw [hT2]
    have hlog : 1 ≤ (1 + Real.log M') ^ 2 := one_le_pow₀ (by
      have := Real.log_nonneg hM'1; linarith)
    set P := (1 + Real.log (7 * k)) ^ 2
    have hP : 0 ≤ P := sq_nonneg _
    have hX : 0 ≤ (A + 16 * B) ^ 2 * (k * Real.sqrt k) * P * Q :=
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) hP) hQ
    have hρ0 : 0 ≤ 125 * (A + 16 * B) * (k * Real.sqrt k) * Q := mul_nonneg (by positivity) hQ
    have h1500 : (1500 : ℝ) ≤ 1521 * l * (1 + Real.log M') ^ 2 :=
      calc (1500 : ℝ) ≤ 1521 * 1 * 1 := by norm_num
        _ ≤ 1521 * l * (1 + Real.log M') ^ 2 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hl1 (by norm_num)) hlog (by norm_num) (by positivity)
    calc _ ≤ (125 * (A + 16 * B) * (k * Real.sqrt k) * Q) * (12 * (A + 16 * B) * P) :=
          mul_le_mul hρ hκ (by positivity) hρ0
      _ = 1500 * ((A + 16 * B) ^ 2 * (k * Real.sqrt k) * P * Q) := by ring
      _ ≤ 1521 * l * (1 + Real.log M') ^ 2 * ((A + 16 * B) ^ 2 * (k * Real.sqrt k) * P * Q) :=
          mul_le_mul_of_nonneg_right h1500 hX
      _ = _ := by ring

/-! ### The cross-block decay law -/

/-- Harmonic series `√(k √k)(1 + log 7k)/k²` of the cross-block bound. -/
def crossBlockHarmonicSeries (k : ℕ) : ℝ :=
  1 / (k : ℝ) ^ 2 * (Real.sqrt (k * Real.sqrt k) * (1 + Real.log (7 * k)))

/-- Dual harmonic series `√l/l²`. -/
def crossBlockDualSeries (l : ℕ) : ℝ := 1 / (l : ℝ) ^ 2 * Real.sqrt l

theorem crossBlockHarmonicSeries_nonneg (k : ℕ) : 0 ≤ crossBlockHarmonicSeries k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [crossBlockHarmonicSeries]
  have : 0 ≤ Real.log (7 * k) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith)
  unfold crossBlockHarmonicSeries; positivity

theorem crossBlockHarmonicSeries_le (k : ℕ) :
    crossBlockHarmonicSeries k ≤ 15 * ((k : ℝ) ^ (9 / 8 : ℝ))⁻¹ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [crossBlockHarmonicSeries]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hs : Real.sqrt (k * Real.sqrt k) = (k : ℝ) ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow k, ← Real.rpow_one_add' hk0.le (by norm_num), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hk0.le]
    norm_num
  have hr : (1 : ℝ) ≤ (k : ℝ) ^ (1 / 8 : ℝ) := Real.one_le_rpow hk1 (by norm_num)
  have hlog : 1 + Real.log (7 * k) ≤ 15 * (k : ℝ) ^ (1 / 8 : ℝ) := by
    rw [Real.log_mul (by norm_num) hk0.ne']
    have h7 : Real.log 7 ≤ 6 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 7)]
    have hlk := Real.log_le_rpow_div hk0.le (by norm_num : (0 : ℝ) < 1 / 8)
    rw [div_div_eq_mul_div, div_one] at hlk
    linarith
  have hsq : (k : ℝ) ^ 2 = (k : ℝ) ^ (7 / 8 : ℝ) * (k : ℝ) ^ (9 / 8 : ℝ) := by
    rw [← Real.rpow_add hk0, ← Real.rpow_natCast]; norm_num
  have h34 : (k : ℝ) ^ (3 / 4 : ℝ) * (k : ℝ) ^ (1 / 8 : ℝ) = (k : ℝ) ^ (7 / 8 : ℝ) := by
    rw [← Real.rpow_add hk0]; norm_num
  unfold crossBlockHarmonicSeries
  rw [hs]
  have hp78 : 0 < (k : ℝ) ^ (7 / 8 : ℝ) := Real.rpow_pos_of_pos hk0 _
  have hp98 : 0 < (k : ℝ) ^ (9 / 8 : ℝ) := Real.rpow_pos_of_pos hk0 _
  calc 1 / (k : ℝ) ^ 2 * ((k : ℝ) ^ (3 / 4 : ℝ) * (1 + Real.log (7 * k))) ≤
        1 / (k : ℝ) ^ 2 * ((k : ℝ) ^ (3 / 4 : ℝ) * (15 * (k : ℝ) ^ (1 / 8 : ℝ))) := by gcongr
    _ = 15 * ((k : ℝ) ^ (9 / 8 : ℝ))⁻¹ := by
        rw [hsq, show (k : ℝ) ^ (3 / 4 : ℝ) * (15 * (k : ℝ) ^ (1 / 8 : ℝ)) =
          15 * ((k : ℝ) ^ (3 / 4 : ℝ) * (k : ℝ) ^ (1 / 8 : ℝ)) by ring, h34]
        field_simp

theorem summable_crossBlockHarmonicSeries : Summable crossBlockHarmonicSeries :=
  Summable.of_nonneg_of_le crossBlockHarmonicSeries_nonneg crossBlockHarmonicSeries_le
    ((Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 9 / 8)).mul_left 15)

theorem crossBlockDualSeries_eq (l : ℕ) : crossBlockDualSeries l = 1 / ((l : ℝ) * Real.sqrt l) := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp [crossBlockDualSeries]
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  have hs : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl0
  unfold crossBlockDualSeries
  rw [show (l : ℝ) ^ 2 = l * Real.sqrt l * Real.sqrt l by rw [mul_assoc, Real.mul_self_sqrt hl0.le]; ring]
  field_simp

theorem summable_crossBlockDualSeries : Summable crossBlockDualSeries :=
  summable_inv_mul_sqrt.congr fun l => (crossBlockDualSeries_eq l).symm

theorem crossBlockDualSeries_nonneg (l : ℕ) : 0 ≤ crossBlockDualSeries l := by
  unfold crossBlockDualSeries; positivity

/-- Harmonic mass `(∑_k √(k√k)(1 + log 7k)/k²)(∑_l √l/l²)` of the cross-block law. -/
def crossBlockHarmonicMass : ℝ := (∑' k, crossBlockHarmonicSeries k) * ∑' l, crossBlockDualSeries l

/-- Cross-block constant `(4/π⁴) · 39 (A + 16B) · Z`. -/
def crossBlockConstant (A B : ℝ) : ℝ := 4 / Real.pi ^ 4 * (39 * (A + 16 * B) * crossBlockHarmonicMass)

private theorem crossBlock_sum_of_harmonic {R : Finset ℕ} {φ : ℕ → ℝ → ℝ}
    (hφ : ∀ r ∈ R, IntegrableOn (φ r) (Ioi 1)) (S S' : Finset ℕ) (b c : ℕ → ℝ) {A B τ : ℝ}
    (hW : 0 ≤ A + 16 * B) (hτ : 0 ≤ τ)
    (hbil : ∀ k l : ℕ, 1 ≤ k → 1 ≤ l →
      |∑ n ∈ S, ∑ n' ∈ S', b n * c n' * ∑ r ∈ R, (ArithmeticFunction.vonMangoldt r : ℝ) / r *
        dyadicCrossKernel (weightCosineTransform (φ r)) k ((l * r : ℕ) : ℝ) n n'| ≤
      39 * (A + 16 * B) * crossBlockHarmonicFactor k l * τ *
        Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n ∈ S', c n ^ 2)) :
    |∑ r ∈ R, (ArithmeticFunction.vonMangoldt r : ℝ) / r * ∫ v in Ioi 1, φ r v *
        (realPhaseCombination S b v * realPhaseCombination S' c (r * v))| ≤
      crossBlockConstant A B * τ * Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n ∈ S', c n ^ 2) := by
  set X := Real.sqrt (∑ n ∈ S, b n ^ 2)
  set Y := Real.sqrt (∑ n ∈ S', c n ^ 2)
  set C := 39 * (A + 16 * B) * τ * X * Y
  have hC : 0 ≤ C := by positivity
  have hprod : Summable fun p : ℕ × ℕ => crossBlockHarmonicSeries p.1 * crossBlockDualSeries p.2 :=
    summable_crossBlockHarmonicSeries.mul_of_nonneg summable_crossBlockDualSeries
      crossBlockHarmonicSeries_nonneg crossBlockDualSeries_nonneg
  have h := abs_sum_integral_weight_dilate_le_of_bilinear (fun r => (ArithmeticFunction.vonMangoldt r : ℝ) / r)
    hφ S S' b c (μ := fun p => C * (crossBlockHarmonicSeries p.1 * crossBlockDualSeries p.2))
    (hprod.mul_left C) (fun p => mul_nonneg hC (mul_nonneg (crossBlockHarmonicSeries_nonneg _)
      (crossBlockDualSeries_nonneg _))) fun p hk hl => by
      have hb := hbil p.1 p.2 hk hl
      have e : 1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2) *
          (39 * (A + 16 * B) * crossBlockHarmonicFactor p.1 p.2 * τ * X * Y) =
          C * (crossBlockHarmonicSeries p.1 * crossBlockDualSeries p.2) := by
        simp only [C, crossBlockHarmonicSeries, crossBlockDualSeries, crossBlockHarmonicFactor]
        ring
      rw [← e]
      exact mul_le_mul_of_nonneg_left hb (by positivity)
  refine h.trans (le_of_eq ?_)
  have hn1 : Summable fun k : ℕ => ‖crossBlockHarmonicSeries k‖ :=
    summable_crossBlockHarmonicSeries.abs.congr fun k => (Real.norm_eq_abs _).symm
  have hn2 : Summable fun l : ℕ => ‖crossBlockDualSeries l‖ :=
    summable_crossBlockDualSeries.abs.congr fun l => (Real.norm_eq_abs _).symm
  rw [tsum_mul_left, ← tsum_mul_tsum_of_summable_norm hn1 hn2]
  simp only [crossBlockConstant, crossBlockHarmonicMass, C]
  ring

/-- **Cross-block decay law, downward order.** For a block `S` at `M` and a smaller block `S'` at
`M' ≤ M`, a finite family of dilations `r ≥ 2` with weights whose cosine transforms are bounded by
`A` and by `B/f²` uniformly in `r`, and any patterns,
`|∑_r (Λ(r)/r) ∫ φ_r B_b(v) B_c(rv) dv| ≤ K(A,B) τ(M', M) ‖b‖ ‖c‖`. -/
theorem abs_sum_integral_crossBlock_down_le {R : Finset ℕ} {φ : ℕ → ℝ → ℝ}
    (hφ : ∀ r ∈ R, IntegrableOn (φ r) (Ioi 1)) {A B : ℝ}
    (hA : ∀ m f, |weightCosineTransform (φ m) f| ≤ A)
    (hB : ∀ m f, f ≠ 0 → |weightCosineTransform (φ m) f| ≤ B / f ^ 2) (hB0 : 0 ≤ B)
    (hR : ∀ r ∈ R, 2 ≤ r) {S S' : Finset ℕ} {M M' : ℕ} (hM' : 1 ≤ M') (hMM : M' ≤ M)
    (hS : DyadicScaleBlock S M) (hS' : DyadicScaleBlock S' M') (b c : ℕ → ℝ) :
    |∑ r ∈ R, (ArithmeticFunction.vonMangoldt r : ℝ) / r * ∫ v in Ioi 1, φ r v *
        (realPhaseCombination S b v * realPhaseCombination S' c (r * v))| ≤
      crossBlockConstant A B * crossBlockDecay M' M *
        Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n ∈ S', c n ^ 2) :=
  crossBlock_sum_of_harmonic hφ S S' b c (by have := (abs_nonneg _).trans (hA 0 0); positivity)
    (crossBlockDecay_nonneg M' M) fun _ _ hk hl =>
      abs_bilinear_crossBlock_down_le hA hB hB0 R hR hM' hMM hS hS' b c hk hl

/-- **Cross-block decay law, upward order.** The same bound when the dilated block is the larger
one (`M ≤ M'`), with decay `τ(M, M')`. -/
theorem abs_sum_integral_crossBlock_up_le {R : Finset ℕ} {φ : ℕ → ℝ → ℝ}
    (hφ : ∀ r ∈ R, IntegrableOn (φ r) (Ioi 1)) {A B : ℝ}
    (hA : ∀ m f, |weightCosineTransform (φ m) f| ≤ A)
    (hB : ∀ m f, f ≠ 0 → |weightCosineTransform (φ m) f| ≤ B / f ^ 2) (hB0 : 0 ≤ B)
    (hR : ∀ r ∈ R, 2 ≤ r) {S S' : Finset ℕ} {M M' : ℕ} (hM : 1 ≤ M) (hMM : M ≤ M')
    (hS : DyadicScaleBlock S M) (hS' : DyadicScaleBlock S' M') (b c : ℕ → ℝ) :
    |∑ r ∈ R, (ArithmeticFunction.vonMangoldt r : ℝ) / r * ∫ v in Ioi 1, φ r v *
        (realPhaseCombination S b v * realPhaseCombination S' c (r * v))| ≤
      crossBlockConstant A B * crossBlockDecay M M' *
        Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n ∈ S', c n ^ 2) :=
  crossBlock_sum_of_harmonic hφ S S' b c (by have := (abs_nonneg _).trans (hA 0 0); positivity)
    (crossBlockDecay_nonneg M M') fun _ _ hk hl =>
      abs_bilinear_crossBlock_up_le hA hB hB0 R hR hM hMM hS hS' b c hk hl

end GaloisForLFunctions.ArithmeticPositivityTheory
