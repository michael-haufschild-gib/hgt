import GaloisForLFunctions.LatticeSectionTheory.DefiniteCountsHaveOffLineZeros
import GaloisForLFunctions.LatticeSectionTheory.TheKunnethRiemannRoch
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.NumericalEquivalenceOnTheScalingSurface

/-!
# The Siegel majorant is the Hodge index

The intersection form of a polar surface is indefinite, so its Gaussian count `Σ e^{−π t x²}`
does not exist. Siegel's remedy is a majorant: for the ample class `A_u = e^u H + e^{−u} V`
(`A_u² = 2`, the **boost** of `A = H + V` by `u`),

    P_u(x) = 2 (x · A_u)² / A_u² − x² = e^{2u} (x·H)² + e^{−2u} (x·V)² + δ(x, x).

* **Majorant law** (`siegelMajorant_nonneg_iff_hodgeIndex`). `P_u ≥ 0` on every class iff the
  Hodge index holds: the majorant is the polar part plus the Castelnuovo–Severi defect.
* **Gaussian counts along a class** (`summable_siegelTerm_iff`, `siegelCount_eq_thetaSum`).
  The count `Σ_{n ∈ ℤ} e^{−π t P_u(n x)}` converges iff `P_u(x) > 0`, and then it is the base count
  `θ(t P_u(x))`, with its Poisson duality. On the scaling surface every such count of a nonzero
  primitive class converges iff RH (`riemannHypothesis_iff_forall_summable_siegelTerm`): a
  Gaussian Poisson summation on the Lorentzian lattice presupposes the sign; it cannot produce it.
* **The split plane at a fixed boost is a rectangular lattice**
  (`hyperbolicPlane_siegelMajorant`). On `⟨H, V⟩` the majorant is `e^{−2u} Q_{e^{2u}}`, the form of
  `ℤ ⊕ e^{2u}ℤ`; for `|u| > 1` its Epstein function has a real zero in `(1/2, 1)`
  (`exists_boost_offLine_zero`). A fixed metric on the split plane selects nothing.
* **Hecke is a boost** (`hyperbolicPlane_siegelMajorant_hecke`). On the index-`p` sublattice
  `ℤH ⊕ pℤV` the majorant at boost `u` is `p` times the majorant at boost `u + ½ log p`.
-/

noncomputable section

open Real

namespace GaloisForLFunctions.LatticeSectionTheory

open ArithmeticCastelnuovoSeveri ArithmeticEffectivityTheory ArithmeticOrientationGeometry

section Majorant

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (S : PolarSurface E)

/-- The ample class boosted by `u`: `A_u = e^u H + e^{−u} V`. -/
def boostAmple (u : ℝ) : E := Real.exp u • S.H + Real.exp (-u) • S.V

theorem pair_boostAmple (u : ℝ) (x : E) :
    S.pair x (boostAmple S u) = Real.exp u * S.pair x S.H + Real.exp (-u) * S.pair x S.V := by
  simp only [boostAmple, map_add, map_smul, smul_eq_mul]

theorem pair_boostAmple_self (u : ℝ) : S.pair (boostAmple S u) (boostAmple S u) = 2 := by
  rw [pair_boostAmple]
  simp only [boostAmple, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, S.pair_H_H, S.pair_V_V, S.pair_H_V, S.pair_V_H]
  have : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  linear_combination 2 * this

/-- **The Siegel majorant** at boost `u`: `P_u(x) = (x · A_u)² − x²`. -/
def siegelMajorant (u : ℝ) (x : E) : ℝ := S.pair x (boostAmple S u) ^ 2 - S.pair x x

/-- The majorant is the boosted polar part plus the Castelnuovo–Severi defect. -/
theorem siegelMajorant_eq (u : ℝ) (x : E) :
    siegelMajorant S u x = Real.exp (2 * u) * S.pair x S.H ^ 2 +
      Real.exp (-(2 * u)) * S.pair x S.V ^ 2 + S.defect x x := by
  rw [siegelMajorant, pair_boostAmple, S.defect_self]
  have h1 : Real.exp u ^ 2 = Real.exp (2 * u) := by rw [← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp (-u) ^ 2 = Real.exp (-(2 * u)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have h3 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [← h1, ← h2]
  linear_combination (2 * S.pair x S.H * S.pair x S.V) * h3

theorem siegelMajorant_smul (u t : ℝ) (x : E) :
    siegelMajorant S u (t • x) = t ^ 2 * siegelMajorant S u x := by
  simp only [siegelMajorant, map_smul, LinearMap.smul_apply, smul_eq_mul]; ring

/-- **Majorant law.** The Siegel majorant is nonnegative iff the Hodge index holds. -/
theorem siegelMajorant_nonneg_iff_hodgeIndex (u : ℝ) :
    (∀ x, 0 ≤ siegelMajorant S u x) ↔ S.HodgeIndex := by
  rw [S.hodgeIndex_iff_castelnuovoSeveri, S.castelnuovoSeveri_iff_defect_nonneg]
  constructor
  · intro h x
    have := h (S.prim x)
    rw [siegelMajorant_eq, S.pair_prim_H, S.pair_prim_V, S.defect_prim] at this
    simpa using this
  · intro h x
    rw [siegelMajorant_eq]
    have := h x
    positivity

/-- The `n`-th term of the Gaussian count along the class `x`. -/
def siegelTerm (u t : ℝ) (x : E) (n : ℤ) : ℝ := Real.exp (-π * t * siegelMajorant S u ((n : ℝ) • x))

/-- The Gaussian count along `x` is the base count at parameter `t P_u(x)`. -/
theorem siegelTerm_eq (u t : ℝ) (x : E) (n : ℤ) :
    siegelTerm S u t x n = Real.exp (-π * (t * siegelMajorant S u x) * (n : ℝ) ^ 2) := by
  rw [siegelTerm, siegelMajorant_smul]; congr 1; ring

/-- **Convergence criterion.** The Gaussian count along `x` converges iff `P_u(x) > 0`. -/
theorem summable_siegelTerm_iff (u : ℝ) {t : ℝ} (ht : 0 < t) (x : E) :
    Summable (siegelTerm S u t x) ↔ 0 < siegelMajorant S u x := by
  constructor
  · intro hs
    by_contra hneg
    push Not at hneg
    have hge : ∀ n : ℤ, 1 ≤ siegelTerm S u t x n := fun n => by
      rw [siegelTerm_eq]
      apply Real.one_le_exp
      have : t * siegelMajorant S u x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le hneg
      have := sq_nonneg (n : ℝ)
      nlinarith [Real.pi_pos, mul_nonneg (mul_nonneg Real.pi_pos.le (neg_nonneg.mpr ‹_›)) this]
    have hev := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    rw [Filter.eventually_cofinite] at hev
    have huniv : {n : ℤ | ¬ siegelTerm S u t x n < 1 / 2} = Set.univ :=
      Set.eq_univ_of_forall fun n => by simp only [Set.mem_setOf_eq, not_lt]; linarith [hge n]
    rw [huniv] at hev
    exact Set.infinite_univ hev
  · intro hpos
    have := summable_thetaSum (mul_pos ht hpos)
    refine this.congr fun n => ?_
    rw [siegelTerm_eq]

/-- On a class with positive majorant the count is the base count `θ(t P_u(x))`. -/
theorem siegelCount_eq_thetaSum (u t : ℝ) (x : E) :
    ∑' n : ℤ, siegelTerm S u t x n = thetaSum (t * siegelMajorant S u x) := by
  rw [thetaSum]; refine tsum_congr fun n => ?_; rw [siegelTerm_eq]

/-- **Gaussian counts of primitive classes and the Hodge index.** If every nonzero primitive class
has a convergent Gaussian count, the Hodge index holds. -/
theorem hodgeIndex_of_forall_summable_siegelTerm (u : ℝ) {t : ℝ} (ht : 0 < t)
    (h : ∀ x, S.pair x S.H = 0 → S.pair x S.V = 0 → x ≠ 0 → Summable (siegelTerm S u t x)) :
    S.HodgeIndex := by
  intro x hH hV
  by_cases hx : x = 0
  · simp [hx]
  have hpos := (summable_siegelTerm_iff S u ht x).mp (h x hH hV hx)
  rw [siegelMajorant_eq, hH, hV, S.defect_self, hH, hV] at hpos
  linarith

end Majorant

/-! ### The scaling surface -/

/-- **RH is the convergence of every primitive Gaussian count of the scaling surface.** -/
theorem riemannHypothesis_iff_forall_summable_siegelTerm (u : ℝ) {t : ℝ} (ht : 0 < t) :
    RiemannHypothesis ↔ ∀ x : ScalingCycle, scalingSurface.pair x scalingSurface.H = 0 →
      scalingSurface.pair x scalingSurface.V = 0 → x ≠ 0 →
        Summable (siegelTerm scalingSurface u t x) := by
  rw [← scalingSurface_hodgeIndex_iff]
  refine ⟨fun hHI x hH hV hx => ?_, hodgeIndex_of_forall_summable_siegelTerm scalingSurface u ht⟩
  rw [summable_siegelTerm_iff _ u ht, siegelMajorant_eq, hH, hV]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero, zero_add]
  have hnn := (scalingSurface.castelnuovoSeveri_iff_defect_nonneg.mp
    (scalingSurface.hodgeIndex_iff_castelnuovoSeveri.mp hHI))
  refine lt_of_le_of_ne (hnn x) fun h0 => hx ?_
  -- a primitive class of zero defect is in the numerical radical
  refine (scalingSurface_pairing_nondegenerate x).mp fun y => ?_
  have hcs := scalingSurface.defect_sq_le_of_hodgeIndex hHI x y
  rw [← h0, zero_mul] at hcs
  have hdy : scalingSurface.defect x y = 0 := by nlinarith [sq_nonneg (scalingSurface.defect x y)]
  have hpair : scalingSurface.pair x y = scalingSurface.polar x y - scalingSurface.defect x y := by
    rw [PolarSurface.defect]; ring
  rw [hpair, hdy, PolarSurface.polar, hH, hV]; ring

/-! ### The split plane -/

/-- **The split plane at a fixed boost is rectangular**: on `⟨H, V⟩` the majorant of `aH + bV` is
`e^{−2u}(a² + e^{4u} b²)`, the form of `ℤ ⊕ e^{2u}ℤ` scaled by `e^{−2u}`. -/
theorem hyperbolicPlane_siegelMajorant (u : ℝ) (a b : ℤ) :
    siegelMajorant hyperbolicPlane u ((a : ℝ), (b : ℝ)) =
      Real.exp (-(2 * u)) * rectForm (Real.exp (2 * u)) (a, b) := by
  rw [siegelMajorant_eq]
  have hd : hyperbolicPlane.defect ((a : ℝ), (b : ℝ)) ((a : ℝ), (b : ℝ)) = 0 := by
    rw [PolarSurface.defect_self]
    simp only [hyperbolicPlane_pair]
    change 2 * ((a : ℝ) * 0 + 1 * (b : ℝ)) * ((a : ℝ) * 1 + 0 * (b : ℝ)) -
      ((a : ℝ) * (b : ℝ) + (a : ℝ) * (b : ℝ)) = 0
    ring
  have hH : hyperbolicPlane.pair ((a : ℝ), (b : ℝ)) hyperbolicPlane.H = b := by
    rw [hyperbolicPlane_pair]; change (a : ℝ) * 0 + 1 * (b : ℝ) = b; ring
  have hV : hyperbolicPlane.pair ((a : ℝ), (b : ℝ)) hyperbolicPlane.V = a := by
    rw [hyperbolicPlane_pair]; change (a : ℝ) * 1 + 0 * (b : ℝ) = a; ring
  rw [hd, hH, hV, rectForm]
  have h4 : Real.exp (2 * u) ^ 2 = Real.exp (2 * u) * Real.exp (2 * u) := sq _
  have hinv : Real.exp (-(2 * u)) * Real.exp (2 * u) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  simp only
  rw [h4]
  linear_combination (-(Real.exp (2 * u) * (b : ℝ) ^ 2)) * hinv

/-- **Fixed boosts are fakes**: for `|u| > 1` the majorant lattice of the split plane at boost `u`
has an Epstein function with a real zero in `(1/2, 1)`. -/
theorem exists_boost_offLine_zero {u : ℝ} (hu : 1 < |u|) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ epsteinLambda (Real.exp (2 * u)) (Real.exp_pos _) σ = 0 := by
  rcases lt_abs.mp hu with h | h
  · exact exists_epsteinLambda_eq_zero (Real.exp_lt_exp.mpr (by linarith))
  · exact exists_epsteinLambda_eq_zero_of_lt (Real.exp_pos _) (Real.exp_lt_exp.mpr (by linarith))

/-- **Hecke is a boost.** On the index-`p` sublattice `ℤH ⊕ pℤV` the majorant at boost `u` is `p`
times the majorant at boost `u + ½ log p`. -/
theorem hyperbolicPlane_siegelMajorant_hecke (u : ℝ) {p : ℝ} (hp : 0 < p) (a b : ℝ) :
    siegelMajorant hyperbolicPlane u (a, p * b) =
      p * siegelMajorant hyperbolicPlane (u + Real.log p / 2) (a, b) := by
  have hdef : ∀ v c d : ℝ, siegelMajorant hyperbolicPlane v (c, d) =
      Real.exp (2 * v) * d ^ 2 + Real.exp (-(2 * v)) * c ^ 2 := by
    intro v c d
    rw [siegelMajorant_eq, PolarSurface.defect_self]
    simp only [hyperbolicPlane_pair]
    change Real.exp (2 * v) * (c * 0 + 1 * d) ^ 2 + Real.exp (-(2 * v)) * (c * 1 + 0 * d) ^ 2 +
      (2 * (c * 0 + 1 * d) * (c * 1 + 0 * d) - (c * d + c * d)) = _
    ring
  rw [hdef, hdef]
  have e1 : Real.exp (2 * (u + Real.log p / 2)) = p * Real.exp (2 * u) := by
    rw [show 2 * (u + Real.log p / 2) = 2 * u + Real.log p by ring, Real.exp_add,
      Real.exp_log hp]; ring
  have e2 : Real.exp (-(2 * (u + Real.log p / 2))) = Real.exp (-(2 * u)) / p := by
    rw [show -(2 * (u + Real.log p / 2)) = -(2 * u) - Real.log p by ring, Real.exp_sub,
      Real.exp_log hp]
  rw [e1, e2]
  field_simp

end GaloisForLFunctions.LatticeSectionTheory
