/-
# Exact two-torus `L⁶` identity for the discrete parabola

This is the literal two-dimensional form of the discrete parabola estimate:
the two unit-circle variables carry the frequencies `n` and `n²`.
Successive applications of finite polynomial Parseval identify the sixth
moment with the squared `L²` mass of the exact `(Σn,Σn²)` triple fibers.
-/
import GaloisForLFunctions.RHTower.BourgainFiniteFourierParseval
import GaloisForLFunctions.RHTower.BourgainParabolaFiberSubpower
import Mathlib.Topology.Algebra.Polynomial

open scoped BigOperators Polynomial

namespace RHTower

noncomputable section

/-- Discrete parabola sum evaluated on two complex variables. -/
def bourgainParabolaTwoTorusSum
    (H : ℕ) (a : Fin H → ℂ) (u v : ℂ) : ℂ :=
  ∑ n : Fin H,
    a n * u ^ bourgainIndex n *
      v ^ (bourgainIndex n ^ (2 : ℕ))

/-- Triple convolution of the two-variable parabola sum. -/
def bourgainParabolaTwoTorusTripleSum
    (H : ℕ) (a : Fin H → ℂ) (u v : ℂ) : ℂ :=
  ∑ h : Fin 3 → Fin H,
    bourgainTripleWeight a h *
      u ^ (bourgainParabolaTripleMoment h).1 *
      v ^ (bourgainParabolaTripleMoment h).2

/-- The triple convolution is the exact cube of the original sum. -/
theorem bourgainParabolaTwoTorusSum_pow_three
    (H : ℕ) (a : Fin H → ℂ) (u v : ℂ) :
    bourgainParabolaTwoTorusSum H a u v ^ (3 : ℕ) =
      bourgainParabolaTwoTorusTripleSum H a u v := by
  rw [bourgainParabolaTwoTorusSum, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro h
  simp only [Fin.prod_univ_three, bourgainTripleWeight,
    bourgainParabolaTripleMoment,
    Fin.sum_univ_three]
  rw [pow_add, pow_add, pow_add, pow_add]
  ring

/-- Fiber amplitude for one attained pair `(Σn,Σn²)`. -/
def bourgainParabolaFiberAmplitude
    (H : ℕ) (a : Fin H → ℂ) (y : ℕ × ℕ) : ℂ :=
  ∑ h ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter
      (fun h => bourgainParabolaTripleMoment h = y),
    bourgainTripleWeight a h

/-- Polynomial in the first torus variable after fixing the second. -/
def bourgainParabolaFirstSlicePolynomial
    (H : ℕ) (a : Fin H → ℂ) (v : ℂ) : ℂ[X] :=
  finiteFrequencyPolynomial
    (Finset.univ : Finset (Fin 3 → Fin H))
    (fun h => (bourgainParabolaTripleMoment h).1)
    (fun h =>
      bourgainTripleWeight a h *
        v ^ (bourgainParabolaTripleMoment h).2)

/-- Evaluation of the first slice is the two-variable triple sum. -/
theorem eval_bourgainParabolaFirstSlicePolynomial
    (H : ℕ) (a : Fin H → ℂ) (u v : ℂ) :
    (bourgainParabolaFirstSlicePolynomial H a v).eval u =
      bourgainParabolaTwoTorusTripleSum H a u v := by
  classical
  rw [bourgainParabolaFirstSlicePolynomial, finiteFrequencyPolynomial,
    Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial,
    bourgainParabolaTwoTorusTripleSum]
  apply Fintype.sum_congr
  intro h
  ring

/-- Polynomial in the second torus variable on a fixed first-moment fiber. -/
def bourgainParabolaSecondSlicePolynomial
    (H : ℕ) (a : Fin H → ℂ) (s : ℕ) : ℂ[X] :=
  finiteFrequencyPolynomial
    ((Finset.univ : Finset (Fin 3 → Fin H)).filter
      (fun h => (bourgainParabolaTripleMoment h).1 = s))
    (fun h => (bourgainParabolaTripleMoment h).2)
    (bourgainTripleWeight a)

/-- The grouped coefficient in the first Parseval step evaluates the
corresponding second-slice polynomial. -/
theorem firstFiberSum_eq_eval_secondSlice
    (H : ℕ) (a : Fin H → ℂ) (s : ℕ) (v : ℂ) :
    (∑ h ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter
        (fun h => (bourgainParabolaTripleMoment h).1 = s),
      bourgainTripleWeight a h *
        v ^ (bourgainParabolaTripleMoment h).2) =
      (bourgainParabolaSecondSlicePolynomial H a s).eval v := by
  classical
  rw [bourgainParabolaSecondSlicePolynomial, finiteFrequencyPolynomial,
    Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]

/-- Intersecting first- and second-coordinate conditions is the full moment
fiber at `(s,q)`. -/
theorem bourgainParabolaNestedFilter_eq_fiber
    (H s q : ℕ) :
    ((Finset.univ : Finset (Fin 3 → Fin H)).filter
        (fun h => (bourgainParabolaTripleMoment h).1 = s)).filter
      (fun h => (bourgainParabolaTripleMoment h).2 = q) =
    (Finset.univ : Finset (Fin 3 → Fin H)).filter
      (fun h => bourgainParabolaTripleMoment h = (s, q)) := by
  classical
  ext h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hfst, hsnd⟩
    exact Prod.ext hfst hsnd
  · intro hpair
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

/-- Exact first Parseval step, with the second variable still fixed. -/
theorem circleAverage_firstSlice_norm_sq
    (H : ℕ) (a : Fin H → ℂ) (v : ℂ) :
    Real.circleAverage
        (fun u =>
          ‖bourgainParabolaTwoTorusTripleSum H a u v‖ ^ (2 : ℕ))
        0 1 =
      ∑ s ∈
          (Finset.univ : Finset (Fin 3 → Fin H)).image
            (fun h => (bourgainParabolaTripleMoment h).1),
        ‖(bourgainParabolaSecondSlicePolynomial H a s).eval v‖ ^
          (2 : ℕ) := by
  rw [show
    (fun u =>
      ‖bourgainParabolaTwoTorusTripleSum H a u v‖ ^ (2 : ℕ)) =
    (fun u =>
      ‖(bourgainParabolaFirstSlicePolynomial H a v).eval u‖ ^ (2 : ℕ)) by
      funext u
      rw [eval_bourgainParabolaFirstSlicePolynomial]]
  rw [bourgainParabolaFirstSlicePolynomial,
    circleAverage_finiteFrequencyPolynomial_norm_sq]
  apply Finset.sum_congr rfl
  intro s _
  rw [firstFiberSum_eq_eval_secondSlice]

/-- For a fixed first moment, second moments are in bijection with attained
moment pairs carrying that first coordinate. -/
theorem sum_secondMomentFibers_eq_sum_momentFiber
    (H : ℕ) (a : Fin H → ℂ) (s : ℕ) :
    (∑ q ∈
        (((Finset.univ : Finset (Fin 3 → Fin H)).filter
          (fun h => (bourgainParabolaTripleMoment h).1 = s)).image
            (fun h => (bourgainParabolaTripleMoment h).2)),
      ‖bourgainParabolaFiberAmplitude H a (s, q)‖ ^ (2 : ℕ)) =
    ∑ y ∈
        ((Finset.univ : Finset (Fin 3 → Fin H)).image
          bourgainParabolaTripleMoment).filter (fun y => y.1 = s),
      ‖bourgainParabolaFiberAmplitude H a y‖ ^ (2 : ℕ) := by
  classical
  apply Finset.sum_bij
      (fun q _ => (s, q))
  · intro q hq
    rw [Finset.mem_filter]
    obtain ⟨h, hh, hqeq⟩ := Finset.mem_image.mp hq
    have hfst := (Finset.mem_filter.mp hh).2
    refine ⟨Finset.mem_image.mpr ⟨h, Finset.mem_univ h, ?_⟩, rfl⟩
    exact Prod.ext hfst hqeq
  · intro q₁ hq₁ q₂ hq₂ heq
    exact congrArg Prod.snd heq
  · intro y hy
    have hyImage := (Finset.mem_filter.mp hy).1
    have hyfst := (Finset.mem_filter.mp hy).2
    obtain ⟨h, -, hmoment⟩ := Finset.mem_image.mp hyImage
    refine ⟨y.2, ?_, ?_⟩
    · exact Finset.mem_image.mpr
        ⟨h, Finset.mem_filter.mpr
          ⟨Finset.mem_univ h, by rw [hmoment]; exact hyfst⟩,
          by rw [hmoment]⟩
    · exact Prod.ext hyfst.symm rfl
  · intro q hq
    rfl

/-- The two successive frequency partitions enumerate every attained moment
pair exactly once. -/
theorem sum_firstSecondMomentFibers_eq_fiberMass
    (H : ℕ) (a : Fin H → ℂ) :
    (∑ s ∈
        (Finset.univ : Finset (Fin 3 → Fin H)).image
          (fun h => (bourgainParabolaTripleMoment h).1),
      ∑ q ∈
          (((Finset.univ : Finset (Fin 3 → Fin H)).filter
            (fun h => (bourgainParabolaTripleMoment h).1 = s)).image
              (fun h => (bourgainParabolaTripleMoment h).2)),
        ‖bourgainParabolaFiberAmplitude H a (s, q)‖ ^ (2 : ℕ)) =
      ∑ y ∈
          (Finset.univ : Finset (Fin 3 → Fin H)).image
            bourgainParabolaTripleMoment,
        ‖bourgainParabolaFiberAmplitude H a y‖ ^ (2 : ℕ) := by
  classical
  let Y :=
    (Finset.univ : Finset (Fin 3 → Fin H)).image
      bourgainParabolaTripleMoment
  let S := Y.image Prod.fst
  calc
    (∑ s ∈
        (Finset.univ : Finset (Fin 3 → Fin H)).image
          (fun h => (bourgainParabolaTripleMoment h).1),
      ∑ q ∈
          (((Finset.univ : Finset (Fin 3 → Fin H)).filter
            (fun h => (bourgainParabolaTripleMoment h).1 = s)).image
              (fun h => (bourgainParabolaTripleMoment h).2)),
        ‖bourgainParabolaFiberAmplitude H a (s, q)‖ ^ (2 : ℕ)) =
      ∑ s ∈ S, ∑ y ∈ Y.filter (fun y => y.1 = s),
        ‖bourgainParabolaFiberAmplitude H a y‖ ^ (2 : ℕ) := by
      have hS :
          (Finset.univ : Finset (Fin 3 → Fin H)).image
              (fun h => (bourgainParabolaTripleMoment h).1) = S := by
        simp only [S, Y, Finset.image_image, Function.comp_def]
      rw [hS]
      apply Finset.sum_congr rfl
      intro s hs
      simpa [Y] using sum_secondMomentFibers_eq_sum_momentFiber H a s
    _ = ∑ y ∈ Y,
        ‖bourgainParabolaFiberAmplitude H a y‖ ^ (2 : ℕ) := by
      exact Finset.sum_fiberwise_of_maps_to
        (s := Y) (t := S) (g := Prod.fst)
        (fun y hy => Finset.mem_image.mpr ⟨y, hy, rfl⟩)
        (fun y => ‖bourgainParabolaFiberAmplitude H a y‖ ^ (2 : ℕ))
    _ = ∑ y ∈
          (Finset.univ : Finset (Fin 3 → Fin H)).image
            bourgainParabolaTripleMoment,
        ‖bourgainParabolaFiberAmplitude H a y‖ ^ (2 : ℕ) := by rfl

/-- Exact iterated two-torus Parseval identity for the triple convolution. -/
theorem circleAverage_circleAverage_parabolaTriple_norm_sq
    (H : ℕ) (a : Fin H → ℂ) :
    Real.circleAverage
        (fun v =>
          Real.circleAverage
            (fun u =>
              ‖bourgainParabolaTwoTorusTripleSum H a u v‖ ^ (2 : ℕ))
            0 1)
        0 1 =
      ∑ y ∈
          (Finset.univ : Finset (Fin 3 → Fin H)).image
            bourgainParabolaTripleMoment,
        ‖bourgainParabolaFiberAmplitude H a y‖ ^ (2 : ℕ) := by
  classical
  let S :=
    (Finset.univ : Finset (Fin 3 → Fin H)).image
      (fun h => (bourgainParabolaTripleMoment h).1)
  calc
    Real.circleAverage
        (fun v =>
          Real.circleAverage
            (fun u =>
              ‖bourgainParabolaTwoTorusTripleSum H a u v‖ ^ (2 : ℕ))
            0 1)
        0 1 =
      Real.circleAverage
        (∑ s ∈ S, fun v =>
          ‖(bourgainParabolaSecondSlicePolynomial H a s).eval v‖ ^
            (2 : ℕ))
        0 1 := by
      apply Real.circleAverage_congr_sphere
      intro v _
      simpa [S, Finset.sum_apply] using
        circleAverage_firstSlice_norm_sq H a v
    _ = ∑ s ∈ S,
        Real.circleAverage
          (fun v =>
            ‖(bourgainParabolaSecondSlicePolynomial H a s).eval v‖ ^
              (2 : ℕ))
          0 1 := by
      rw [Real.circleAverage_sum]
      intro s hs
      have hcont :=
        (bourgainParabolaSecondSlicePolynomial H a s).continuous.norm.pow 2
      exact hcont.continuousOn.circleIntegrable (by norm_num)
    _ = ∑ s ∈ S,
        ∑ q ∈
          (((Finset.univ : Finset (Fin 3 → Fin H)).filter
            (fun h => (bourgainParabolaTripleMoment h).1 = s)).image
              (fun h => (bourgainParabolaTripleMoment h).2)),
          ‖bourgainParabolaFiberAmplitude H a (s, q)‖ ^ (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [bourgainParabolaSecondSlicePolynomial,
        circleAverage_finiteFrequencyPolynomial_norm_sq]
      apply Finset.sum_congr rfl
      intro q hq
      rw [bourgainParabolaNestedFilter_eq_fiber]
      rfl
    _ = ∑ y ∈
          (Finset.univ : Finset (Fin 3 → Fin H)).image
            bourgainParabolaTripleMoment,
        ‖bourgainParabolaFiberAmplitude H a y‖ ^ (2 : ℕ) :=
      sum_firstSecondMomentFibers_eq_fiberMass H a

/-- Exact two-torus sixth moment identity for the original parabola sum. -/
theorem circleAverage_circleAverage_parabola_norm_pow_six
    (H : ℕ) (a : Fin H → ℂ) :
    Real.circleAverage
        (fun v =>
          Real.circleAverage
            (fun u =>
              ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (6 : ℕ))
            0 1)
        0 1 =
      ∑ y ∈
          (Finset.univ : Finset (Fin 3 → Fin H)).image
            bourgainParabolaTripleMoment,
        ‖bourgainParabolaFiberAmplitude H a y‖ ^ (2 : ℕ) := by
  rw [← circleAverage_circleAverage_parabolaTriple_norm_sq H a]
  apply Real.circleAverage_congr_sphere
  intro v _
  apply Real.circleAverage_congr_sphere
  intro u _
  change
    ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (6 : ℕ) =
      ‖bourgainParabolaTwoTorusTripleSum H a u v‖ ^ (2 : ℕ)
  rw [← bourgainParabolaTwoTorusSum_pow_three H a u v, norm_pow]
  ring

/-- **Literal discrete parabola `L⁶` estimate on the two-torus.** -/
theorem circleAverage_circleAverage_parabola_norm_pow_six_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (a : Fin H → ℂ),
        Real.circleAverage
            (fun v =>
              Real.circleAverage
                (fun u =>
                  ‖bourgainParabolaTwoTorusSum H a u v‖ ^ (6 : ℕ))
                0 1)
            0 1 ≤
          C * (H : ℝ) ^ ε *
            (∑ n : Fin H, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  obtain ⟨C, hC, hfiber⟩ := bourgainParabolaFiberL2_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H a
  rw [circleAverage_circleAverage_parabola_norm_pow_six]
  exact hfiber H a

end

end RHTower
