import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.DisorderTails
import GaloisForLFunctions.HTGeometry.DiagonalPatchConstruction

/-! # First-excursion moments at fixed total interaction strength -/
open MeasureTheory ProbabilityTheory Filter Set
namespace GaloisForLFunctions.HTGeometry.WeakBonds
open PrescribedTimes
noncomputable section

/-- Euclidean length of the vector of independent physical couplings. -/
def coefficientNorm {n : ℕ} (x : PrefixIndex n → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (PrefixIndex n))‖

/-- Scale a prefix to the prescribed Euclidean coupling norm. -/
def atRadius {n : ℕ} (r : ℝ) (x : PrefixIndex n → ℝ) := (r/coefficientNorm x) • x

theorem coefficientNorm_atRadius {n : ℕ} (x : PrefixIndex n → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hx : 0 < coefficientNorm x) : coefficientNorm (atRadius r x) = r := by
  change ‖(r/coefficientNorm x) • (WithLp.toLp 2 x : EuclideanSpace ℝ (PrefixIndex n))‖ = r
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hr hx.le)]
  exact div_mul_cancel₀ _ hx.ne'

private theorem retained_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) {bulk : Set ℝ} (x : ι → ℝ) (h : x ∈ retainedSector S bulk)
    (i : ι) (hi : i ∉ S) : x i ∈ bulk := by
  have hx := h i (mem_univ i)
  change x i ∈ (if i ∈ S then univ else bulk) at hx
  rwa [if_neg hi] at hx

private theorem coordinate_norm_bound {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) :
    x i ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ :=
  (le_abs_self (x i)).trans (abs_coord_le_norm (WithLp.toLp 2 x) i)

private theorem retained_norm {n : ℕ} (a b : Fin (n+1)) (x : PrefixIndex n → ℝ)
    (hx : x ∈ retainedSector (cutSet a b) (Icc 1 2)) : 1 ≤ coefficientNorm x := by
  let site : Fin (n+2) × Fin 3 := (0,0)
  let i : PrefixIndex n := (pathCoeffEquiv n).symm (Sum.inl site)
  have hxi : x i ∈ Icc (1:ℝ) 2 := retained_coordinate (cutSet a b) x hx i
    (onsite_not_in_cutSet a b site)
  exact hxi.1.trans (coordinate_norm_bound x i)

private theorem not_integrable_atRadius {n : ℕ} {μ : Measure (PrefixIndex n → ℝ)}
    (J : (PrefixIndex n → ℝ) → ℝ) (hJ : Measurable J)
    (hhom : ∀ q : ℝ, 0 < q → ∀ x, q*J (q • x) = J x)
    {Q : Set (PrefixIndex n → ℝ)} (hQ : MeasurableSet Q)
    (hR : ∀ x ∈ Q, 1 ≤ coefficientNorm x)
    (hinf : ¬ Integrable (fun x => |Q.indicator J x|^18) μ)
    (r : ℝ) (hr : 0 < r) : ¬ Integrable (fun x => |J (atRadius r x)|^18) μ := by
  intro hint
  apply hinf
  have hmoment : Measurable (fun x => |Q.indicator J x|^18) := by
    simpa only [Real.norm_eq_abs] using (hJ.indicator hQ).norm.pow_const (18:ℕ)
  apply (hint.const_mul (r^18)).mono' hmoment.aestronglyMeasurable
  filter_upwards with x
  change ‖|Q.indicator J x|^18‖ ≤ r^18*|J (atRadius r x)|^18
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  by_cases h : x ∈ Q
  · rw [indicator_of_mem h]
    have hx := hR x h
    let q := r/coefficientNorm x
    have hq : 0 < q := div_pos hr (zero_lt_one.trans_le hx)
    have hscale : q*J (atRadius r x) = J x := hhom q hq x
    have habs : |J x| = q*|J (atRadius r x)| := by
      calc
        _ = |q*J (atRadius r x)| := congrArg abs hscale.symm
        _ = _ := by rw [abs_mul,abs_of_pos hq]
    calc
      |J x|^18 = (q*|J (atRadius r x)|)^18 := congrArg (fun z : ℝ => z^18) habs
      _ ≤ _ := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq.le (div_le_self hr.le hx) 18)
          (pow_nonneg (abs_nonneg _) _)
  · rw [indicator_of_notMem h,abs_zero,zero_pow (by decide : 18 ≠ 0)]
    exact mul_nonneg (pow_nonneg hr.le _) (pow_nonneg (abs_nonneg _) _)

/-- Fix the total norm of each Gaussian draw at any positive radius, including
the square root of the number of coefficients. The smaller of the onset and
actual first wait still has infinite eighteenth absolute moment. -/
theorem gaussian_fixed_radius_first_excursion_moment :
    ∀ᶠ k : ℕ in atTop,
      let P := nearHilbertContinuousCircuitBudget (k+3)
      let μ := Measure.pi (fun _ : PrefixIndex (k+1) => gaussianReal 0 1)
      ∀ r : ℝ, 0 < r → ∀ s ≤ P/2,
        ¬ Integrable (fun x => |min (crossingOrigin (k+1) P (9/80) (atRadius r x))
          (crossingWait (k+1) P s (atRadius r x))|^18) μ := by
  filter_upwards [gaussian_two_weak_bonds_moment] with k hk
  intro P μ r hr s hs
  obtain ⟨a,b,_,hcut⟩ := hk
  let J := fun x => min (crossingOrigin (k+1) P (9/80) x) (crossingWait (k+1) P s x)
  have hJ : Measurable J := (measurable_crossingOrigin _ _ _).min (measurable_crossingWait _ _ _)
  refine not_integrable_atRadius J hJ ?_ (measurable_retainedSector (cutSet a b) measurableSet_Icc)
    (retained_norm a b) (hcut s hs) r hr
  intro q hq x
  dsimp only [J]
  rw [mul_min_of_nonneg _ _ hq.le,smul_crossingOrigin _ _ _ hq,smul_crossingWait _ _ _ hq]

#print axioms gaussian_fixed_radius_first_excursion_moment
end
end GaloisForLFunctions.HTGeometry.WeakBonds
