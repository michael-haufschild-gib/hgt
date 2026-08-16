import GaloisForLFunctions.HTGeometry.GermWeierstrassPreparation
import GaloisForLFunctions.HTGeometry.GermLinearEquiv
import GaloisForLFunctions.HTGeometry.PolydiscWeierstrass

/-!
# Weierstrass preparation as an identity in the ring of germs

The analytic preparation on a polydisc, read in the local ring: a germ regular in the distinguished
coordinate is a distinguished polynomial in `germCoord` with coefficients pulled back from the germ
ring in the remaining variables and vanishing at the origin, times a unit.

This is the form the factorization theory uses, because it is an identity between elements of a
ring rather than between functions on a polydisc.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Metric

variable {n : ℕ}

/-- The polydisc of a preparation. -/
def prepPolydisc (t δ : ℝ) : Set (Fin (n + 1) → ℂ) :=
  {w : Fin (n + 1) → ℂ | Fin.tail w ∈ ball (0 : Fin n → ℂ) δ ∧ ‖w 0‖ < t}

theorem isOpen_prepPolydisc (t δ : ℝ) : IsOpen (prepPolydisc (n := n) t δ) := by
  have h1 : IsOpen {w : Fin (n + 1) → ℂ | Fin.tail w ∈ ball (0 : Fin n → ℂ) δ} :=
    isOpen_ball.preimage
      ((HTGeometry.tailLin : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ)).continuous)
  have h2 : IsOpen {w : Fin (n + 1) → ℂ | ‖w 0‖ < t} := by
    have : Continuous fun w : Fin (n + 1) → ℂ => ‖w 0‖ :=
      (continuous_apply (0 : Fin (n + 1))).norm
    exact isOpen_lt this continuous_const
  exact h1.inter h2

theorem zero_mem_prepPolydisc {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) :
    (0 : Fin (n + 1) → ℂ) ∈ prepPolydisc (n := n) t δ := by
  refine ⟨?_, ?_⟩
  · have : Fin.tail (0 : Fin (n + 1) → ℂ) = (0 : Fin n → ℂ) := by
      funext i
      simp [Fin.tail]
    rw [this]
    exact mem_ball_self hδ
  · simpa using ht


/-- The coercion of the low-degree part of a germ polynomial. -/
theorem coe_germPolyTail {d : ℕ} {a : ℕ → (Fin n → ℂ) → ℂ}
    (haA : ∀ j, AnalyticAt ℂ (a j) (0 : Fin n → ℂ)) :
    ((∑ j ∈ Finset.range d, germTail n (analyticGermOf (haA j)) * germCoord n ^ j :
        AnalyticGerm (0 : Fin (n + 1) → ℂ)) : Germ (𝓝 (0 : Fin (n + 1) → ℂ)) ℂ)
      = ((fun w : Fin (n + 1) → ℂ =>
          ∑ j ∈ Finset.range d, a j (Fin.tail w) * (w 0) ^ j) :
            (Fin (n + 1) → ℂ) → ℂ) := by
  classical
  have hmapsum : ((∑ j ∈ Finset.range d,
        germTail n (analyticGermOf (haA j)) * germCoord n ^ j :
          AnalyticGerm (0 : Fin (n + 1) → ℂ)) : Germ (𝓝 (0 : Fin (n + 1) → ℂ)) ℂ)
      = ∑ j ∈ Finset.range d,
          (((germTail n (analyticGermOf (haA j)) * germCoord n ^ j :
            AnalyticGerm (0 : Fin (n + 1) → ℂ)) : Germ (𝓝 (0 : Fin (n + 1) → ℂ)) ℂ)) :=
    map_sum (analyticGermSubring (0 : Fin (n + 1) → ℂ)).subtype _ _
  rw [hmapsum]
  have hterm : ∀ j ∈ Finset.range d,
      (((germTail n (analyticGermOf (haA j)) * germCoord n ^ j :
          AnalyticGerm (0 : Fin (n + 1) → ℂ)) : Germ (𝓝 (0 : Fin (n + 1) → ℂ)) ℂ))
        = ((fun w : Fin (n + 1) → ℂ => a j (Fin.tail w) * (w 0) ^ j) :
            (Fin (n + 1) → ℂ) → ℂ) := by
    intro j _
    rw [Subring.coe_mul, SubmonoidClass.coe_pow, germTail_analyticGermOf (haA j)]
    rfl
  rw [Finset.sum_congr rfl hterm, ← Germ.coe_sum]
  congr 1
  funext w
  simp

/-- The coercion of a distinguished polynomial in the germ ring is the germ of the explicit
polynomial function. -/
theorem coe_germDistinguished {d : ℕ} {a : ℕ → (Fin n → ℂ) → ℂ}
    (haA : ∀ j, AnalyticAt ℂ (a j) (0 : Fin n → ℂ)) :
    (((germCoord n ^ d
        + ∑ j ∈ Finset.range d, germTail n (analyticGermOf (haA j)) * germCoord n ^ j :
          AnalyticGerm (0 : Fin (n + 1) → ℂ))) : Germ (𝓝 (0 : Fin (n + 1) → ℂ)) ℂ)
      = ((fun w : Fin (n + 1) → ℂ =>
          (w 0) ^ d + ∑ j ∈ Finset.range d, a j (Fin.tail w) * (w 0) ^ j) :
            (Fin (n + 1) → ℂ) → ℂ) := by
  rw [Subring.coe_add, SubmonoidClass.coe_pow, coe_germPolyTail haA]
  rfl

/-- **Weierstrass preparation as an identity of germs.** -/
theorem germ_preparation_algebraic {f : (Fin (n + 1) → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f (0 : Fin (n + 1) → ℂ))
    (hreg : ¬ (fun z : ℂ => f (Fin.cons z (0 : Fin n → ℂ))) =ᶠ[𝓝 (0 : ℂ)] 0) :
    ∃ (d : ℕ) (α : ℕ → AnalyticGerm (0 : Fin n → ℂ)) (u : AnalyticGerm (0 : Fin (n + 1) → ℂ)),
      IsUnit u ∧ (∀ j, j < d → analyticGermValue (0 : Fin n → ℂ) (α j) = 0) ∧
      analyticGermOf hf
        = (germCoord n ^ d + ∑ j ∈ Finset.range d, germTail n (α j) * germCoord n ^ j) * u := by
  classical
  obtain ⟨r, hr, hfr⟩ := exists_ball_analyticOnNhd hf
  have hfd : DifferentiableOn ℂ f (ball (0 : Fin (n + 1) → ℂ) r) := hfr.differentiableOn
  obtain ⟨t, δ, d, a, u, htpos, hδpos, hadiff, hazero, hudiff, hmain⟩ :=
    HTGeometry.germ_weierstrass_preparation isOpen_ball (mem_ball_self hr) hfd hreg
  -- germs of the coefficients
  have haA : ∀ j, AnalyticAt ℂ (a j) (0 : Fin n → ℂ) := fun j =>
    HTGeometry.analyticAt_of_differentiableOn isOpen_ball (hadiff j) (mem_ball_self hδpos)
  have huA : AnalyticAt ℂ u (0 : Fin (n + 1) → ℂ) :=
    HTGeometry.analyticAt_of_differentiableOn (isOpen_prepPolydisc t δ) hudiff
      (zero_mem_prepPolydisc htpos hδpos)
  have hcons0 : (Fin.cons (0 : ℂ) (0 : Fin n → ℂ) : Fin (n + 1) → ℂ) = 0 := by
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp
  have hu0 : u (0 : Fin (n + 1) → ℂ) ≠ 0 := by
    have := (hmain 0 (mem_ball_self hδpos) 0 (by simpa using htpos)).2
    rwa [hcons0] at this
  refine ⟨d, fun j => analyticGermOf (haA j), analyticGermOf huA, ?_, ?_, ?_⟩
  · rw [isUnit_analyticGerm_iff, analyticGermValue_of huA]
    exact hu0
  · intro j hj
    rw [analyticGermValue_of (haA j)]
    exact hazero j hj
  -- the germ identity
  refine Subtype.ext ?_
  have hcoe : (((germCoord n ^ d
        + ∑ j ∈ Finset.range d, germTail n (analyticGermOf (haA j)) * germCoord n ^ j)
      * analyticGermOf huA : AnalyticGerm (0 : Fin (n + 1) → ℂ)) : Germ (𝓝 (0 : Fin (n + 1) → ℂ)) ℂ)
      = ((fun w : Fin (n + 1) → ℂ =>
          ((w 0) ^ d + ∑ j ∈ Finset.range d, a j (Fin.tail w) * (w 0) ^ j) * u w) :
            (Fin (n + 1) → ℂ) → ℂ) := by
    rw [Subring.coe_mul, coe_germDistinguished haA]
    rfl
  rw [hcoe]
  refine (Germ.coe_eq.mpr ?_).symm
  filter_upwards [(isOpen_prepPolydisc t δ).mem_nhds (zero_mem_prepPolydisc htpos hδpos)]
    with w hw
  obtain ⟨hw1, hw2⟩ := hw
  have hmainw := (hmain (Fin.tail w) hw1 (w 0) hw2).1
  rw [Fin.cons_self_tail] at hmainw
  exact hmainw.symm

end GaloisForLFunctions.HTGeometry
