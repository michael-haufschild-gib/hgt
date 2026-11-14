import GaloisForLFunctions.HilbertMetric.NonoverlappingCoverObstructions
import GaloisForLFunctions.MetaplecticMobiusDescent.EisensteinNearestPoint
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.LatticeSeparation

/-!
# Disk coverings of the actual Eisenstein lattice

The lattice embedding used by the cubic metaplectic theory has a closed
coverability locus, stable finite obstructions, and norm-multiplication
monotonicity. Its sharp nearest-point bound controls every Voronoi cell
of a covering and transfers planar obstructions to fine lattice samples.

These are the mechanisms of Propositions 3.4 and 9.3 and Lemmas 7.3 and 9.1
of Kittipassorn--Phetmak--Sriamorn, applied to the corpus's integral model.
-/

noncomputable section
namespace GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskCovering

open HilbertMetric Metric Set

/-- The triangular lattice at a real scale, in the fixed complex embedding. -/
def point (d : ℝ) (n : O) : ℂ := (d : ℂ) * ringComplex n

/-- Coverability by closed unit disks with distinct centres at distance at least two. -/
def CoverableSpacing (d : ℝ) : Prop := BallCoverable 1 (point d)

theorem continuous_point : Continuous (fun d : ℝ => point d) :=
  continuous_pi fun _ => Complex.continuous_ofReal.mul continuous_const

/-- The coverable scales form a closed subset of the whole real line. -/
theorem isClosed_coverableSpacing : IsClosed {d | CoverableSpacing d} :=
  isClosed_coverable_parameters 1 point continuous_point

theorem isOpen_noncoverableSpacing : IsOpen {d | ¬ CoverableSpacing d} :=
  isClosed_coverableSpacing.isOpen_compl

/-- The collapsed lattice is covered by the disk centred at zero. -/
theorem coverableSpacing_zero : CoverableSpacing 0 := by
  refine ⟨fun _ => 0, fun n => ?_, fun _ _ => Or.inl rfl⟩
  simp only [point, Complex.ofReal_zero, zero_mul, dist_self, NNReal.coe_one]
  exact zero_le_one

/-- At spacing at least two, the lattice points themselves are admissible centres. -/
theorem coverableSpacing_of_two_le {d : ℝ} (hd : 2 ≤ d) : CoverableSpacing d := by
  have hd0 : 0 ≤ d := (by positivity : (0 : ℝ) ≤ 2).trans hd
  refine ⟨point d, fun n => ?_, fun n m => ?_⟩
  · simpa only [dist_self, NNReal.coe_one] using (zero_le_one : (0 : ℝ) ≤ 1)
  · by_cases hnm : n = m
    · exact Or.inl (congrArg (point d) hnm)
    · right
      simp only [NNReal.coe_one, mul_one, point, dist_eq_norm, ← mul_sub, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd0]
      have hnorm : 1 ≤ ‖ringComplex n - ringComplex m‖ := by
        simpa only [dist_eq_norm] using one_le_dist_ringComplex hnm
      have hmul := mul_le_mul_of_nonneg_left hnorm hd0
      linarith only [hmul, hd]

/-- Every obstruction is witnessed by finitely many actual algebraic integers. -/
theorem noncoverableSpacing_iff_finset (d : ℝ) :
    ¬ CoverableSpacing d ↔
      ∃ s : Finset O, ¬ BallCoverable 1 (fun n : s => point d n) :=
  not_ballCoverable_iff_finset 1 (point d)

/-- Integral dilation selects a sublattice. -/
theorem coverableSpacing_int_mul (d : ℝ) (m : ℤ) :
    CoverableSpacing d → CoverableSpacing ((m : ℝ) * d) := by
  intro h
  have hc := h.comp (fun n : O => (m : O) * n)
  have heq : point d ∘ (fun n : O => (m : O) * n) = point ((m : ℝ) * d) := by
    funext n
    simp only [Function.comp_apply, point, map_mul, map_intCast, Complex.ofReal_mul,
      Complex.ofReal_intCast]
    ring
  rw [heq] at hc
  exact hc

/-- Multiplication by any Eisenstein integer gives a rotated sublattice. -/
theorem coverableSpacing_norm_mul (d : ℝ) (α : O) :
    CoverableSpacing d → CoverableSpacing (‖ringComplex α‖ * d) := by
  intro h
  by_cases hα : α = 0
  · subst α
    simpa only [map_zero, norm_zero, zero_mul] using coverableSpacing_zero
  have hαc : ringComplex α ≠ 0 := by
    intro hz
    exact hα (ringComplex_injective (by simpa only [map_zero] using hz))
  let u : ℂ := (‖ringComplex α‖ : ℂ) / ringComplex α
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr hαc)
  have hp (n : O) : point (‖ringComplex α‖ * d) n = u * point d (α * n) := by
    simp only [point, u, map_mul, Complex.ofReal_mul]
    field_simp
  have hd (x y : ℂ) : dist (u * x) (u * y) = dist x y := by
    rw [dist_eq_norm, ← mul_sub, norm_mul, hu, one_mul, dist_eq_norm]
  obtain ⟨c, hc, hs⟩ := h
  refine ⟨fun n => u * c (α * n), fun n => ?_, fun n m => ?_⟩
  · rw [hp, hd]
    exact hc (α * n)
  · rcases hs (α * n) (α * m) with he | he
    · exact Or.inl (congrArg (u * ·) he)
    · exact Or.inr (by rw [hd]; exact he)

/-- The norm sublattice implication also transports noncoverability backwards. -/
theorem noncoverableSpacing_of_norm_mul (d : ℝ) (α : O) :
    ¬ CoverableSpacing (‖ringComplex α‖ * d) → ¬ CoverableSpacing d :=
  fun h hc => h (coverableSpacing_norm_mul d α hc)

/-- Scaling the sharp nearest-point estimate gives squared error at most `d²/3`. -/
theorem exists_point_dist_sq_le (d : ℝ) (hd : d ≠ 0) (z : ℂ) :
    ∃ n : O, dist z (point d n) ^ 2 ≤ d ^ 2 / 3 := by
  obtain ⟨n, hn⟩ := exists_eisenstein_distance_sq_le_third (z / (d : ℂ))
  have hdc : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  have heq : z - point d n = (d : ℂ) * (z / (d : ℂ) - ringComplex n) := by
    dsimp [point]
    field_simp
  refine ⟨n, ?_⟩
  rw [dist_eq_norm, heq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Complex.normSq_eq_norm_sq] at hn
  nlinarith only [mul_le_mul_of_nonneg_left hn (sq_nonneg d)]

/-- Every point lies within the scaled hexagonal covering radius of the lattice. -/
theorem exists_point_dist_le (d : ℝ) (hd : d ≠ 0) (z : ℂ) :
    ∃ n : O, dist z (point d n) ≤ Real.sqrt (d ^ 2 / 3) := by
  obtain ⟨n, hn⟩ := exists_point_dist_sq_le d hd z
  exact ⟨n, (Real.le_sqrt (dist_nonneg) (by positivity)).mpr hn⟩

/-- The nearest-centre cell of a unit-disk covering has radius at most `1+|d|/√3`. -/
theorem covering_voronoi_bound (d : ℝ) (hd : d ≠ 0) (c : O → ℂ)
    (hc : ∀ n, dist (point d n) (c n) ≤ 1) (i : O) (x : ℂ)
    (hnearest : ∀ n, dist x (c i) ≤ dist x (c n)) :
    dist x (c i) ≤ 1 + Real.sqrt (d ^ 2 / 3) := by
  obtain ⟨n, hn⟩ := exists_point_dist_le d hd x
  calc
    dist x (c i) ≤ dist x (c n) := hnearest n
    _ ≤ dist x (point d n) + dist (point d n) (c n) := dist_triangle _ _ _
    _ ≤ Real.sqrt (d ^ 2 / 3) + 1 := add_le_add hn (hc n)
    _ = 1 + Real.sqrt (d ^ 2 / 3) := add_comm _ _

/-- A finite witness continues to obstruct nearby spacings with the same labels. -/
theorem noncoverableSpacing_iff_stable_finset (d : ℝ) :
    ¬ CoverableSpacing d ↔ ∃ (s : Finset O) (ε : ℝ), 0 < ε ∧
      ∀ d' : ℝ, dist d' d < ε → ¬ BallCoverable 1 (fun n : s => point d' n) := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := (noncoverableSpacing_iff_finset d).mp h
    have hc : Continuous (fun t : ℝ => fun n : s => point t n) :=
      continuous_pi fun n => (continuous_apply (n : O)).comp continuous_point
    obtain ⟨ε, hε, he⟩ := Metric.isOpen_iff.mp
      (isOpen_noncoverable_parameters 1 _ hc) d hs
    exact ⟨s, ε, hε, fun d' hd' => he hd'⟩
  · rintro ⟨s, ε, hε, h⟩ hd
    exact h d (by simpa only [dist_self] using hε) (hd.comp Subtype.val)

/-- Every planar obstruction can be rounded into all sufficiently fine triangular lattices. -/
theorem round_noncoverable_configuration {ι : Type*} (p : ι → ℂ)
    (hp : ¬ BallCoverable 1 p) :
    ∃ ε > 0, ∀ d : ℝ, 0 < d → d < ε →
      ∃ n : ι → O, ¬ BallCoverable 1 (fun i => point d (n i)) := by
  obtain ⟨s, ε, hε, hstable⟩ := (not_ballCoverable_iff_robust_finset 1 p).mp hp
  refine ⟨ε, hε, fun d hd hdε => ?_⟩
  choose n hn using (fun i => exists_point_dist_sq_le d hd.ne' (p i))
  refine ⟨n, hstable (fun i => point d (n i)) (fun i _ => ?_)⟩
  rw [dist_comm]
  have hsqrt : Real.sqrt (d ^ 2 / 3) ≤ d :=
    Real.sqrt_le_iff.mpr ⟨hd.le, by nlinarith only [sq_nonneg d]⟩
  exact (((Real.le_sqrt dist_nonneg (by positivity)).mpr (hn i)).trans hsqrt).trans_lt hdε

end GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskCovering

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskCovering.isClosed_coverableSpacing
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskCovering.coverableSpacing_of_two_le
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskCovering.coverableSpacing_norm_mul
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskCovering.covering_voronoi_bound
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskCovering.round_noncoverable_configuration
