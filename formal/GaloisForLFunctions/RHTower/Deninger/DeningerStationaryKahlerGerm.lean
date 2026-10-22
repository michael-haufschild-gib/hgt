import GaloisForLFunctions.RHTower.Deninger.DeningerLeafwiseKahler
import GaloisForLFunctions.RHTower.Deninger.DeningerReesJetTower
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Real.Sqrt

/-!
# The stationary Kähler--conormal product germ

The three-real-dimensional germ `ℂ_z × ℝ_r` carries the involution `σ(z, r) = (conj z, -r)` and the
conformal flow `φ^t(z, r) = (e^{t/2} z, e^{-t} r)`.  The flow commutes with the involution, so it
descends to the quotient; the invariant transverse coordinate of the quotient is `x = r²`, on which
the descended flow is the contraction `x ↦ e^{-2t} x`, and the apex `(0, 0)` is its unique
stationary point on the preserved real leaf `r = 0`.

The tangent space at the apex splits into the leaf plane and the transverse line.  The two blocks
carry the two incompatible weights of the construction: the flow scales the leaf coordinate by
`e^{t/2}`, hence the leafwise Kähler form by `e^{t}`, while it scales the transverse orbifold
coordinate by `e^{-2t}`.  The two weights agree only at `t = 0`, so no coordinate carries both.

The involution reverses leaf orientation, so the Kähler form and the Hodge star descend only through
the orientation sign local system: an invariant multiple of the Kähler form vanishes, and the star
exchanges invariant and anti-invariant one-forms.

* `deningerGermFlow_sigma`, `deningerGermFlow_add` : the flow descends to the quotient.
* `deningerGermTransverse_flow` : the transverse exponent is `-2`.
* `deningerGermIota_equivariant` : the real-place transverse embedding.
* `deningerGerm_finrank`, `deningerGermLeafBlock_finrank` : dimension three, codimension one.
* `deningerGermWeight_ne` : the leaf and transverse weights are independent.
* `deningerGermSigmaOne_wedge`, `deningerGermSigmaOne_star` : the orientation-sign Hodge laws.
* `deningerGermJetTower_character` : the complete dual-conormal even-jet character.
-/

namespace RHTower

open scoped ComplexConjugate

section StationaryGerm

/-- The real involution of the oriented cover: complex conjugation on the leaf together with the
reflection of the transverse coordinate. -/
def deningerGermSigma (p : ℂ × ℝ) : ℂ × ℝ := (conj p.1, -p.2)

/-- The stationary conformal flow of the oriented cover. -/
noncomputable def deningerGermFlow (t : ℝ) (p : ℂ × ℝ) : ℂ × ℝ :=
  (Real.exp (t / 2) • p.1, Real.exp (-t) * p.2)

/-- The invariant transverse coordinate of the quotient germ. -/
def deningerGermTransverse (p : ℂ × ℝ) : ℝ := p.2 ^ (2 : ℕ)

/-- **The involution is an involution.** -/
theorem deningerGermSigma_involutive : Function.Involutive deningerGermSigma := by
  rintro ⟨z, r⟩
  simp [deningerGermSigma]

/-- The involution is real linear, so the quotient is a real orbifold. -/
theorem deningerGermSigma_smul (c : ℝ) (p : ℂ × ℝ) :
    deningerGermSigma (c • p) = c • deningerGermSigma p := by
  rcases p with ⟨z, r⟩
  simp [deningerGermSigma, Complex.real_smul, Complex.conj_ofReal]

theorem deningerGermSigma_add (p q : ℂ × ℝ) :
    deningerGermSigma (p + q) = deningerGermSigma p + deningerGermSigma q := by
  rcases p with ⟨z, r⟩
  rcases q with ⟨w, s⟩
  simp [deningerGermSigma, Prod.ext_iff]
  ring

/-- **The fixed locus of the involution is the real axis of the preserved leaf.**  The quotient is
therefore an orbifold precisely along `L_∞`. -/
theorem deningerGermSigma_fixed_iff (p : ℂ × ℝ) :
    deningerGermSigma p = p ↔ (p.1.im = 0 ∧ p.2 = 0) := by
  rcases p with ⟨z, r⟩
  simp only [deningerGermSigma, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨Complex.conj_eq_iff_im.mp h1, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Complex.conj_eq_iff_im.mpr h1, by rw [h2, neg_zero]⟩

/-- The flow at time zero is the identity. -/
theorem deningerGermFlow_zero (p : ℂ × ℝ) : deningerGermFlow 0 p = p := by
  simp [deningerGermFlow]

/-- **The flow is a one-parameter group.** -/
theorem deningerGermFlow_add (t s : ℝ) (p : ℂ × ℝ) :
    deningerGermFlow (t + s) p = deningerGermFlow t (deningerGermFlow s p) := by
  rcases p with ⟨z, r⟩
  refine Prod.ext ?_ ?_
  · show Real.exp ((t + s) / 2) • z = Real.exp (t / 2) • Real.exp (s / 2) • z
    rw [smul_smul, ← Real.exp_add]
    congr 2
    ring
  · show Real.exp (-(t + s)) * r = Real.exp (-t) * (Real.exp (-s) * r)
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring

/-- **The flow commutes with the involution**, hence descends to the quotient germ. -/
theorem deningerGermFlow_sigma (t : ℝ) (p : ℂ × ℝ) :
    deningerGermSigma (deningerGermFlow t p) = deningerGermFlow t (deningerGermSigma p) := by
  rcases p with ⟨z, r⟩
  refine Prod.ext ?_ ?_
  · show conj (Real.exp (t / 2) • z) = Real.exp (t / 2) • conj z
    rw [Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]
  · show -(Real.exp (-t) * r) = Real.exp (-t) * -r
    ring

/-- The transverse coordinate is invariant under the involution, so it is a function on the
quotient germ. -/
theorem deningerGermTransverse_sigma (p : ℂ × ℝ) :
    deningerGermTransverse (deningerGermSigma p) = deningerGermTransverse p := by
  rcases p with ⟨z, r⟩
  show (-r) ^ (2 : ℕ) = r ^ (2 : ℕ)
  ring

/-- **The transverse coordinate separates the involution orbits.**  Its fibres over the leaf are
exactly the pairs `{r, -r}`, so `x = r²` is the transverse coordinate downstairs. -/
theorem deningerGermTransverse_fiber {p q : ℂ × ℝ}
    (h : deningerGermTransverse p = deningerGermTransverse q) : q.2 = p.2 ∨ q.2 = -p.2 := by
  have h' : q.2 ^ (2 : ℕ) = p.2 ^ (2 : ℕ) := h.symm
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h'

/-- **The transverse exponent is `-2`.**  The descended flow contracts the orbifold coordinate by
`e^{-2t}`, so it is exactly Deninger's real-place Rees flow. -/
theorem deningerGermTransverse_flow (t : ℝ) (p : ℂ × ℝ) :
    deningerGermTransverse (deningerGermFlow t p)
      = deningerReesFlow t (deningerGermTransverse p) := by
  rcases p with ⟨z, r⟩
  show (Real.exp (-t) * r) ^ (2 : ℕ) = Real.exp (-2 * t) * r ^ (2 : ℕ)
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  ring

/-- **The apex is stationary.** -/
theorem deningerGermFlow_apex (t : ℝ) : deningerGermFlow t (0, 0) = (0, 0) := by
  simp [deningerGermFlow]

/-- **The apex is the only stationary point.** -/
theorem deningerGermFlow_fixed_iff {p : ℂ × ℝ} (h : ∀ t : ℝ, deningerGermFlow t p = p) :
    p = (0, 0) := by
  have h1 := congrArg Prod.fst (h 2)
  have h2 := congrArg Prod.snd (h 2)
  refine Prod.ext ?_ ?_
  · show p.1 = 0
    have hz : Real.exp (2 / 2) • p.1 = p.1 := h1
    rw [Complex.real_smul] at hz
    have hne : ((Real.exp (2 / 2) : ℝ) : ℂ) - 1 ≠ 0 := by
      rw [sub_ne_zero]
      intro hcon
      have hreal : Real.exp (2 / 2) = 1 := by exact_mod_cast hcon
      rw [Real.exp_eq_one_iff] at hreal
      norm_num at hreal
    have := sub_eq_zero.mpr hz
    rw [← sub_one_mul] at this
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hne
    · exact h'
  · show p.2 = 0
    have hr : Real.exp (-2) * p.2 = p.2 := h2
    have hne : Real.exp (-2) - 1 ≠ 0 := by
      have : Real.exp (-2) ≠ 1 := by
        rw [Ne, Real.exp_eq_one_iff]
        norm_num
      exact sub_ne_zero.mpr this
    have := sub_eq_zero.mpr hr
    rw [← sub_one_mul] at this
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hne
    · exact h'

/-- **The preserved leaf.**  The flow preserves the leaf `r = 0`, and preserves its complement. -/
theorem deningerGermFlow_leaf_iff (t : ℝ) (p : ℂ × ℝ) :
    (deningerGermFlow t p).2 = 0 ↔ p.2 = 0 := by
  show Real.exp (-t) * p.2 = 0 ↔ p.2 = 0
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (ne_of_gt (Real.exp_pos _))
    · exact h
  · intro h
    exact Or.inr h

/-- The involution acts on the preserved leaf by complex conjugation, so the leaf downstairs is the
real quotient `ℂ / (z ↦ conj z)`. -/
theorem deningerGermSigma_leaf (z : ℂ) : deningerGermSigma (z, 0) = (conj z, 0) := by
  simp [deningerGermSigma]

/-- The real-place transverse embedding, induced by the equivariant lift `r ↦ (0, r)`. -/
noncomputable def deningerGermIota (x : ℝ) : ℂ × ℝ := (0, Real.sqrt x)

/-- The transverse embedding is a section of the transverse coordinate: it is transverse to the
leaf distribution. -/
theorem deningerGermTransverse_iota {x : ℝ} (hx : 0 ≤ x) :
    deningerGermTransverse (deningerGermIota x) = x := by
  show Real.sqrt x ^ (2 : ℕ) = x
  rw [Real.sq_sqrt hx]

/-- **The transverse embedding meets the preserved leaf only at the apex.** -/
theorem deningerGermIota_leaf_iff {x : ℝ} (hx : 0 ≤ x) :
    (deningerGermIota x).2 = 0 ↔ x = 0 := by
  show Real.sqrt x = 0 ↔ x = 0
  rw [Real.sqrt_eq_zero hx]

/-- **Equivariance of the transverse embedding.**  Composing the embedding with the germ flow is
the same as contracting the parameter by `e^{-2t}`. -/
theorem deningerGermIota_equivariant (t x : ℝ) :
    deningerGermFlow t (deningerGermIota x) = deningerGermIota (deningerReesFlow t x) := by
  refine Prod.ext ?_ ?_
  · show Real.exp (t / 2) • (0 : ℂ) = 0
    simp
  · show Real.exp (-t) * Real.sqrt x = Real.sqrt (Real.exp (-2 * t) * x)
    rw [Real.sqrt_mul (le_of_lt (Real.exp_pos _))]
    congr 1
    have hsq : Real.exp (-2 * t) = Real.exp (-t) ^ (2 : ℕ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hsq, Real.sqrt_sq (le_of_lt (Real.exp_pos _))]

/-- The transverse embedding is injective on the closed half line. -/
theorem deningerGermIota_injOn {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : deningerGermIota x = deningerGermIota y) : x = y := by
  have h2 : Real.sqrt x = Real.sqrt y := congrArg Prod.snd h
  rw [← Real.sq_sqrt hx, ← Real.sq_sqrt hy, h2]

end StationaryGerm

section TangentBlocks

/-- **The germ has real dimension three.** -/
theorem deningerGerm_finrank : Module.finrank ℝ (ℂ × ℝ) = 3 := by
  rw [Module.finrank_prod, Complex.finrank_real_complex, Module.finrank_self]

/-- The tangent block of the leaf foliation: the kernel of the transverse projection. -/
noncomputable def deningerGermLeafBlock : Submodule ℝ (ℂ × ℝ) := LinearMap.ker (LinearMap.snd ℝ ℂ ℝ)

theorem deningerGermLeafBlock_mem_iff (p : ℂ × ℝ) :
    p ∈ deningerGermLeafBlock ↔ p.2 = 0 := Iff.rfl

theorem deningerGermTransverseProj_range :
    LinearMap.range (LinearMap.snd ℝ ℂ ℝ) = ⊤ :=
  LinearMap.range_eq_top.mpr fun r => ⟨(0, r), rfl⟩

/-- **The foliation has codimension one**: the leaf block is a real plane inside the
three-dimensional germ. -/
theorem deningerGermLeafBlock_finrank : Module.finrank ℝ deningerGermLeafBlock = 2 := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (LinearMap.snd ℝ ℂ ℝ)
  rw [deningerGerm_finrank, deningerGermTransverseProj_range, finrank_top,
    Module.finrank_self] at hrk
  show Module.finrank ℝ (LinearMap.ker (LinearMap.snd ℝ ℂ ℝ)) = 2
  omega

/-- **The flow acts on the leaf block by the half-density weight `e^{t/2}`.** -/
theorem deningerGermFlow_leafBlock {p : ℂ × ℝ} (hp : p ∈ deningerGermLeafBlock) (t : ℝ) :
    deningerGermFlow t p = Real.exp (t / 2) • p := by
  have hp2 : p.2 = 0 := hp
  refine Prod.ext rfl ?_
  show Real.exp (-t) * p.2 = Real.exp (t / 2) * p.2
  rw [hp2, mul_zero, mul_zero]

/-- The leaf half-density weight. -/
noncomputable def deningerGermLeafWeight (t : ℝ) : ℝ := Real.exp (t / 2)

/-- The transverse orbifold weight. -/
noncomputable def deningerGermTransverseWeight (t : ℝ) : ℝ := Real.exp (-2 * t)

/-- **The two tangent blocks carry independent weights.**  The leaf half-density weight and the
transverse orbifold weight agree only at time zero, so no coordinate of the germ carries both. -/
theorem deningerGermWeight_ne {t : ℝ} (ht : t ≠ 0) :
    deningerGermLeafWeight t ≠ deningerGermTransverseWeight t := by
  intro h
  rw [deningerGermLeafWeight, deningerGermTransverseWeight, Real.exp_eq_exp] at h
  exact ht (by linarith)

/-- The leaf weight is the square root of the Kähler weight, and the transverse weight is the
inverse square of the linear normal weight: the two are the two ends of the germ's weight
spectrum. -/
theorem deningerGermLeafWeight_sq (t : ℝ) :
    deningerGermLeafWeight t ^ (2 : ℕ) = Real.exp t := by
  rw [deningerGermLeafWeight, ← Real.exp_nat_mul]
  congr 1
  ring

theorem deningerGermTransverseWeight_eq (t : ℝ) :
    deningerGermTransverseWeight t = Real.exp (-t) ^ (2 : ℕ) := by
  rw [deningerGermTransverseWeight, ← Real.exp_nat_mul]
  congr 1
  ring

/-- **The leafwise Kähler weight is one.**  The flow scales the leafwise Kähler form by `e^{t}`,
the square of the leaf half-density weight. -/
theorem deningerGermKahler_weight (t : ℝ) (a b : ℝ × ℝ) :
    deningerLeafWedge (deningerGermLeafWeight t • a) (deningerGermLeafWeight t • b)
      = Real.exp t * deningerLeafWedge a b :=
  deningerLeafFlow_wedge t a b

end TangentBlocks

section OrientationSign

/-- The involution acting on leafwise one-forms: it fixes `dX` and reverses `dY`. -/
def deningerGermSigmaOne (a : ℝ × ℝ) : ℝ × ℝ := (a.1, -a.2)

theorem deningerGermSigmaOne_involutive : Function.Involutive deningerGermSigmaOne := by
  rintro ⟨x, y⟩
  simp [deningerGermSigmaOne]

/-- **The involution reverses leaf orientation.** -/
theorem deningerGermSigmaOne_wedge (a b : ℝ × ℝ) :
    deningerLeafWedge (deningerGermSigmaOne a) (deningerGermSigmaOne b)
      = -deningerLeafWedge a b := by
  rcases a with ⟨x, y⟩
  rcases b with ⟨z, w⟩
  simp only [deningerGermSigmaOne, deningerLeafWedge]
  ring

/-- **The involution anticommutes with the Hodge star.** -/
theorem deningerGermSigmaOne_star (a : ℝ × ℝ) :
    deningerGermSigmaOne (deningerLeafStar a) = -deningerLeafStar (deningerGermSigmaOne a) := by
  rcases a with ⟨x, y⟩
  simp only [deningerGermSigmaOne, deningerLeafStar, Prod.neg_mk, neg_neg]

/-- **The Kähler form descends only through the orientation sign local system.**  An invariant
multiple of the leafwise Kähler form vanishes. -/
theorem deningerGermKahler_invariant_eq_zero {c : ℝ}
    (h : ∀ a b : ℝ × ℝ, c * deningerLeafWedge (deningerGermSigmaOne a) (deningerGermSigmaOne b)
      = c * deningerLeafWedge a b) : c = 0 := by
  have h1 := h (1, 0) (0, 1)
  rw [deningerGermSigmaOne_wedge] at h1
  have hw : deningerLeafWedge ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) = 1 := by
    simp [deningerLeafWedge]
  rw [hw, mul_one, mul_neg, mul_one] at h1
  linarith

/-- **The Hodge star exchanges untwisted and orientation-sign one-forms.** -/
theorem deningerGermStar_of_invariant {a : ℝ × ℝ} (ha : deningerGermSigmaOne a = a) :
    deningerGermSigmaOne (deningerLeafStar a) = -deningerLeafStar a := by
  rw [deningerGermSigmaOne_star, ha]

theorem deningerGermStar_of_antiInvariant {a : ℝ × ℝ} (ha : deningerGermSigmaOne a = -a) :
    deningerGermSigmaOne (deningerLeafStar a) = deningerLeafStar a := by
  rw [deningerGermSigmaOne_star, ha]
  rcases a with ⟨x, y⟩
  simp only [deningerLeafStar, Prod.neg_mk, neg_neg]

/-- The complexified odd Hodge operator `J = ⋆ c` on leafwise one-forms. -/
def deningerGermJ (a : (ℝ × ℝ) × (ℝ × ℝ)) : (ℝ × ℝ) × (ℝ × ℝ) :=
  (deningerLeafStar a.1, -deningerLeafStar a.2)

/-- **The odd Hodge operator squares to `-1`.** -/
theorem deningerGermJ_sq (a : (ℝ × ℝ) × (ℝ × ℝ)) : deningerGermJ (deningerGermJ a) = -a := by
  refine Prod.ext ?_ ?_
  · show deningerLeafStar (deningerLeafStar a.1) = -a.1
    rw [deningerLeafStar_star]
  · show -deningerLeafStar (-deningerLeafStar a.2) = -a.2
    rcases a.2 with ⟨x, y⟩
    simp only [deningerLeafStar, Prod.neg_mk, neg_neg]

/-- **The odd Hodge density is positive.**  The cup trace of a nonzero complexified one-form
against its `J`-image is the sum of the squared lengths of its real and imaginary parts. -/
theorem deningerGermJ_pos (a : (ℝ × ℝ) × (ℝ × ℝ)) :
    deningerLeafWedge a.1 (deningerGermJ a).1 - deningerLeafWedge a.2 (deningerGermJ a).2
      = (a.1.1 ^ (2 : ℕ) + a.1.2 ^ (2 : ℕ)) + (a.2.1 ^ (2 : ℕ) + a.2.2 ^ (2 : ℕ)) := by
  show deningerLeafWedge a.1 (deningerLeafStar a.1)
      - deningerLeafWedge a.2 (-deningerLeafStar a.2) = _
  have h2 : deningerLeafWedge a.2 (-deningerLeafStar a.2)
      = -deningerLeafWedge a.2 (deningerLeafStar a.2) := by
    rcases a.2 with ⟨x, y⟩
    simp only [deningerLeafWedge, deningerLeafStar, Prod.neg_mk]
    ring
  rw [h2, deningerLeafWedge_star, deningerLeafWedge_star, sub_neg_eq_add]

theorem deningerGermJ_pos_of_ne {a : (ℝ × ℝ) × (ℝ × ℝ)} (ha : a ≠ 0) :
    0 < deningerLeafWedge a.1 (deningerGermJ a).1 - deningerLeafWedge a.2 (deningerGermJ a).2 := by
  rw [deningerGermJ_pos]
  rcases a with ⟨u, v⟩
  by_cases hu : u = 0
  · have hv : v ≠ 0 := fun hv => ha (by rw [hu, hv]; rfl)
    have hpos : 0 < deningerLeafWedge v (deningerLeafStar v) := deningerLeafWedge_star_pos hv
    rw [deningerLeafWedge_star] at hpos
    have hnn : 0 ≤ u.1 ^ (2 : ℕ) + u.2 ^ (2 : ℕ) := by positivity
    simpa using by linarith
  · have hpos : 0 < deningerLeafWedge u (deningerLeafStar u) := deningerLeafWedge_star_pos hu
    rw [deningerLeafWedge_star] at hpos
    have hnn : 0 ≤ v.1 ^ (2 : ℕ) + v.2 ^ (2 : ℕ) := by positivity
    simpa using by linarith

end OrientationSign

section DualConormalCharacter

/-- **The transverse pullback along the germ flow is the Rees pullback of the coordinate germ.** -/
theorem deningerGermPullback (f : ℝ → ℝ) (t : ℝ) (p : ℂ × ℝ) :
    f (deningerGermTransverse (deningerGermFlow t p))
      = (fun x => f (deningerReesFlow t x)) (deningerGermTransverse p) := by
  rw [deningerGermTransverse_flow]

/-- **The dual-conormal jet law of the germ.**  Each normalized transverse jet is an eigenline of
the germ flow of weight `e^{-2kt}`. -/
theorem deningerGermJet_flow {k : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ k f) (t : ℝ) :
    deningerRealJet k (fun x => f (deningerReesFlow t x))
      = deningerGermTransverseWeight ((k : ℝ) * t) * deningerRealJet k f := by
  have hw : deningerGermTransverseWeight ((k : ℝ) * t) = deningerJetWeight t k := by
    rw [deningerGermTransverseWeight, deningerJetWeight]
    congr 1
    ring
  rw [hw, deningerRealJet_reesFlow hf]

/-- **The complete dual-conormal even-jet character of the germ.** -/
theorem deningerGermJetTower_character {t : ℝ} (ht : 0 < t) :
    ∑' k : ℕ, deningerGermTransverseWeight ((k : ℝ) * t) = (1 - Real.exp (-2 * t))⁻¹ := by
  rw [← deningerJetTower_tsum ht]
  refine tsum_congr fun k => ?_
  rw [deningerGermTransverseWeight]
  congr 1
  ring

end DualConormalCharacter

end RHTower
