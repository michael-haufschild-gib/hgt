import GaloisForLFunctions.HTGeometry.StripHullHolomorphic
import GaloisForLFunctions.HTGeometry.LineJetTransfer

/-!
# The strip carrier is separated by the central line

Two ingredients.  First, if the evaluation of a Bohr curve is isometric — the distance between two
values equals the distance between the two translates — then distinct carrier points have distinct
values, so the carrier embeds in the value space.  For the vertical translate curve of a function on
a closed substrip this holds outright: the substrip is invariant under vertical translation, so the
orbit distance *is* the value distance.

Second, carrier points are holomorphic on the open substrip, so two of them agreeing on the central
line agree everywhere by the identity theorem, hence are equal.  This is the separation the jet
embedding needs: a carrier point is determined by its restriction to the line.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

/-- **An isometric evaluation separates the carrier.** -/
theorem bohrEval_injective_of_isometry {f : ℝ →ᵇ E}
    (hiso : ∀ s t : ℝ, dist (f s) (f t) = dist (translateBC s f) (translateBC t f)) :
    Function.Injective (bohrEval f) := by
  have hcont : Continuous (bohrEval f) :=
    UniformSpace.Completion.continuous_extension
  have hdist : ∀ x y : BohrHull f, dist (bohrEval f x) (bohrEval f y) = dist x y := by
    intro x y
    induction x, y using UniformSpace.Completion.induction_on₂ with
    | hp =>
      exact isClosed_eq (by fun_prop) continuous_dist
    | ih s t =>
      have hs : bohrEval f (s : BohrHull f) = f s.val :=
        UniformSpace.Completion.extension_coe (BohrLine.uniformContinuous_eval f) s
      have ht : bohrEval f (t : BohrHull f) = f t.val :=
        UniformSpace.Completion.extension_coe (BohrLine.uniformContinuous_eval f) t
      rw [hs, ht, UniformSpace.Completion.dist_eq, BohrLine.dist_eq]
      exact hiso s.val t.val
  intro x y hxy
  have h := hdist x y
  rw [hxy, dist_self] at h
  exact dist_eq_zero.mp h.symm

/-- **The vertical translate curve evaluates isometrically.**  A closed vertical substrip is
invariant under vertical translation, so the supremum over the orbit adds nothing. -/
theorem dist_stripCurve_eq {σ r : ℝ} {F : ℂ → ℂ} {G : ℝ →ᵇ ((closedStrip σ r) →ᵇ ℂ)}
    (hG : ∀ (τ : ℝ) (z : closedStrip σ r), G τ z = F ((z : ℂ) + (τ : ℂ) * Complex.I)) (s t : ℝ) :
    dist (G s) (G t) = dist (translateBC s G) (translateBC t G) := by
  refine le_antisymm ?_ ?_
  · have h := BoundedContinuousFunction.dist_coe_le_dist
      (f := translateBC s G) (g := translateBC t G) 0
    simpa using h
  · refine (BoundedContinuousFunction.dist_le dist_nonneg).mpr fun τ => ?_
    refine (BoundedContinuousFunction.dist_le dist_nonneg).mpr fun z => ?_
    have hmem : ((z : ℂ) + (τ : ℂ) * Complex.I) ∈ closedStrip σ r := by
      have : ((z : ℂ) + (τ : ℂ) * Complex.I).re = (z : ℂ).re := by simp
      show |(((z : ℂ) + (τ : ℂ) * Complex.I)).re - σ| ≤ r
      rw [this]
      exact z.2
    have hs : (translateBC s G) τ z = F ((z : ℂ) + ((τ + s : ℝ) : ℂ) * Complex.I) := by
      rw [translateBC_apply, hG]
    have ht : (translateBC t G) τ z = F ((z : ℂ) + ((τ + t : ℝ) : ℂ) * Complex.I) := by
      rw [translateBC_apply, hG]
    have hs' : G s ⟨(z : ℂ) + (τ : ℂ) * Complex.I, hmem⟩
        = F ((z : ℂ) + ((τ + s : ℝ) : ℂ) * Complex.I) := by
      rw [hG]
      push_cast
      ring_nf
    have ht' : G t ⟨(z : ℂ) + (τ : ℂ) * Complex.I, hmem⟩
        = F ((z : ℂ) + ((τ + t : ℝ) : ℂ) * Complex.I) := by
      rw [hG]
      push_cast
      ring_nf
    rw [hs, ht, ← hs', ← ht']
    exact BoundedContinuousFunction.dist_coe_le_dist _

/-- A bounded continuous function on a closed vertical substrip is determined by its values on the
open substrip. -/
theorem eq_of_eqOn_verticalStrip_closed {σ r : ℝ} (hr : 0 < r) {u v : (closedStrip σ r) →ᵇ ℂ}
    (h : ∀ z : closedStrip σ r, (z : ℂ) ∈ verticalStrip σ r → u z = v z) : u = v := by
  ext z
  set a : ℝ := (z : ℂ).re - σ with ha
  have hz : |a| ≤ r := z.2
  have hmem : ∀ n : ℕ, ((σ : ℂ) + (((1 - 1 / (n + 1 : ℝ)) * a : ℝ) : ℂ)
      + ((z : ℂ).im : ℂ) * Complex.I) ∈ closedStrip σ r := by
    intro n
    have hcoef : (0 : ℝ) ≤ 1 - 1 / (n + 1 : ℝ) := by
      have hpos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
      rw [sub_nonneg, div_le_one hpos]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hle : 1 - 1 / (n + 1 : ℝ) ≤ 1 := by
      have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
      linarith
    show |((σ : ℂ) + (((1 - 1 / (n + 1 : ℝ)) * a : ℝ) : ℂ)
      + ((z : ℂ).im : ℂ) * Complex.I).re - σ| ≤ r
    have hre : ((σ : ℂ) + (((1 - 1 / (n + 1 : ℝ)) * a : ℝ) : ℂ)
        + ((z : ℂ).im : ℂ) * Complex.I).re = σ + (1 - 1 / (n + 1 : ℝ)) * a := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, sub_zero, mul_one, add_zero]
    rw [hre]
    have : |σ + (1 - 1 / (n + 1 : ℝ)) * a - σ| = (1 - 1 / (n + 1 : ℝ)) * |a| := by
      rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hcoef]
    rw [this]
    calc (1 - 1 / (n + 1 : ℝ)) * |a| ≤ 1 * |a| := by
          exact mul_le_mul_of_nonneg_right hle (abs_nonneg a)
      _ = |a| := one_mul _
      _ ≤ r := hz
  have hopen : ∀ n : ℕ, ((σ : ℂ) + (((1 - 1 / (n + 1 : ℝ)) * a : ℝ) : ℂ)
      + ((z : ℂ).im : ℂ) * Complex.I) ∈ verticalStrip σ r := by
    intro n
    have hcoef : (0 : ℝ) ≤ 1 - 1 / (n + 1 : ℝ) := by
      have hpos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
      rw [sub_nonneg, div_le_one hpos]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hstrict : (1 - 1 / (n + 1 : ℝ)) * |a| < r := by
      rcases eq_or_lt_of_le (abs_nonneg a) with h0 | h0
      · rw [← h0, mul_zero]
        exact hr
      · have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
        nlinarith
    show |((σ : ℂ) + (((1 - 1 / (n + 1 : ℝ)) * a : ℝ) : ℂ)
      + ((z : ℂ).im : ℂ) * Complex.I).re - σ| < r
    have hre : ((σ : ℂ) + (((1 - 1 / (n + 1 : ℝ)) * a : ℝ) : ℂ)
        + ((z : ℂ).im : ℂ) * Complex.I).re = σ + (1 - 1 / (n + 1 : ℝ)) * a := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, sub_zero, mul_one, add_zero]
    rw [hre, add_sub_cancel_left, abs_mul, abs_of_nonneg hcoef]
    exact hstrict
  -- the approximating sequence converges to `z`
  have hzval : (σ : ℂ) + ((a : ℝ) : ℂ) + ((z : ℂ).im : ℂ) * Complex.I = (z : ℂ) := by
    have hre : ((a : ℝ) : ℂ) = ((z : ℂ).re : ℂ) - (σ : ℂ) := by
      rw [ha]
      push_cast
      ring
    rw [hre]
    have hri := Complex.re_add_im (z : ℂ)
    linear_combination hri
  have hcoefTend : Filter.Tendsto (fun n : ℕ => ((1 - 1 / (n + 1 : ℝ)) * a : ℝ))
      Filter.atTop (nhds a) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - 1 / (n + 1 : ℝ))
        Filter.atTop (nhds 1) := by
      have h0 : Filter.Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
        tendsto_const_nhds
      simpa using hconst.sub h0
    have hconsta : Filter.Tendsto (fun _ : ℕ => a) Filter.atTop (nhds a) := tendsto_const_nhds
    have h2 := h1.mul hconsta
    simpa using h2
  have htend : Filter.Tendsto
      (fun n : ℕ => ((σ : ℂ) + (((1 - 1 / (n + 1 : ℝ)) * a : ℝ) : ℂ)
        + ((z : ℂ).im : ℂ) * Complex.I)) Filter.atTop
      (nhds ((σ : ℂ) + ((a : ℝ) : ℂ) + ((z : ℂ).im : ℂ) * Complex.I)) :=
    (tendsto_const_nhds.add
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hcoefTend)).add tendsto_const_nhds
  rw [hzval] at htend
  have hsub : Filter.Tendsto (fun n : ℕ => (⟨_, hmem n⟩ : closedStrip σ r))
      Filter.atTop (nhds z) := by
    rw [tendsto_subtype_rng]
    exact htend
  have hu := (u.continuous.tendsto z).comp hsub
  have hv := (v.continuous.tendsto z).comp hsub
  have heqn : ∀ n : ℕ, u (⟨_, hmem n⟩ : closedStrip σ r) = v ⟨_, hmem n⟩ :=
    fun n => h _ (hopen n)
  refine tendsto_nhds_unique hu ?_
  refine hv.congr fun n => ?_
  exact (heqn n).symm

/-- **A carrier point is determined by its restriction to the central line.**  Carrier points are
holomorphic on the open substrip, so two agreeing on the line agree on the substrip by the identity
theorem, and the isometric evaluation then identifies them. -/
theorem hull_eq_of_line_eq {σ R r : ℝ} {F : ℂ → ℂ} (hr0 : 0 < r) (hr : r < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R))
    {Gb : ℝ →ᵇ ((closedStrip σ r) →ᵇ ℂ)}
    (hGb : ∀ (τ : ℝ) (z : closedStrip σ r), Gb τ z = F ((z : ℂ) + (τ : ℂ) * Complex.I))
    {x y : BohrHull Gb}
    (hline : ∀ (t : ℝ) (hz : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ closedStrip σ r),
      bohrEval Gb x ⟨_, hz⟩ = bohrEval Gb y ⟨_, hz⟩) :
    x = y := by
  obtain ⟨gx, hgx, hgxv⟩ := exists_holomorphic_of_hull hr hF hGb x
  obtain ⟨gy, hgy, hgyv⟩ := exists_holomorphic_of_hull hr hF hGb y
  have hmemline : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ closedStrip σ r := by
    intro t
    show |((σ : ℂ) + (t : ℂ) * Complex.I).re - σ| ≤ r
    have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
    rw [hre, sub_self, abs_zero]
    exact hr0.le
  have hlineg : ∀ t : ℝ,
      gx ((σ : ℂ) + (t : ℂ) * Complex.I) = gy ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    rw [hgxv ⟨_, hmemline t⟩, hgyv ⟨_, hmemline t⟩]
    exact hline t (hmemline t)
  have heq := eqOn_of_eqOn_line hr0 hgx hgy hlineg
  refine bohrEval_injective_of_isometry (dist_stripCurve_eq hGb) ?_
  refine eq_of_eqOn_verticalStrip_closed hr0 fun z hzopen => ?_
  rw [← hgxv z, ← hgyv z]
  exact heq hzopen

end GaloisForLFunctions
