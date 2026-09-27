import GaloisForLFunctions.RHTower.CCMFiniteTriangleBound
import GaloisForLFunctions.RHTower.CCMPrimeFrustratedTriangle

/-!
# The prime-triangle gain survives arbitrary finite source extensions

The constructed arithmetic triangle is inserted into an otherwise arbitrary
finite family. Its positive correction remains valid after every new coupling
is included. The denominator records the edge budget used in the global bound.
-/

noncomputable section

open scoped BigOperators

namespace RHTower

def ccmWeilTriangleExtension {ι : Type*} {a : SuzukiPositiveAperture}
    (u v w : CCMArchimedeanFormDomain a) (extra : ι → CCMArchimedeanFormDomain a) :
    Fin 3 ⊕ ι → CCMArchimedeanFormDomain a :=
  Sum.elim (fun i => if i = 0 then u else if i = 1 then v else w) extra

theorem ccmWeilTriangleExtension_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : SuzukiPositiveAperture) (u v w : CCMArchimedeanFormDomain a)
    (extra : ι → CCMArchimedeanFormDomain a) (x : Fin 3 ⊕ ι → ℝ) :
    let f := ccmWeilTriangleExtension u v w extra
    finiteSignedSeparateLower (fun i j => ccmWeilRealPolar a (f i) (f j)) x +
      signedTriangleGain (ccmWeilRealPolar a u v) (ccmWeilRealPolar a u w) (ccmWeilRealPolar a v w) *
        (x (Sum.inl 0) ^ 2 + x (Sum.inl 1) ^ 2 + x (Sum.inl 2) ^ 2) /
          (6 * max 1 ((Fintype.card (Fin 3 ⊕ ι) : ℝ) - 2)) ≤
      ccmRestrictedWeilSourceQuadratic a (∑ i, (x i : ℂ) • f i) := by
  let f := ccmWeilTriangleExtension u v w extra
  let M := fun i j => ccmWeilRealPolar a (f i) (f j)
  have h₁ : finiteSignedOffDiagonal M (Sum.inl 0) (Sum.inl 1) = ccmWeilRealPolar a u v := by
    simp [M, f, finiteSignedOffDiagonal, ccmWeilTriangleExtension]
  have h₂ : finiteSignedOffDiagonal M (Sum.inl 0) (Sum.inl 2) = ccmWeilRealPolar a u w := by
    simp [M, f, finiteSignedOffDiagonal, ccmWeilTriangleExtension]
  have h₃ : finiteSignedOffDiagonal M (Sum.inl 1) (Sum.inl 2) = ccmWeilRealPolar a v w := by
    simp [M, f, finiteSignedOffDiagonal, ccmWeilTriangleExtension]
  have hg := single_triangle_le_finiteSignedTriangleCorrection M x (Sum.inl 0) (Sum.inl 1) (Sum.inl 2)
  rw [h₁, h₂, h₃] at hg
  have h := ccmRestrictedWeilSourceQuadratic_finite_triangle_lower a f x
  change finiteSignedSeparateLower M x + _ ≤ _
  linarith only [hg, h]

/-- A genuine positive arithmetic correction, valid with every finite extension and every coefficient vector. -/
theorem exists_cofinal_ccmPrime_triangle_extension_gain {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) :
    ∃ (p q : ℕ) (r m : ℝ) (a : SuzukiPositiveAperture)
      (u v w : CCMComplexSmoothInteriorSource a),
      N ≤ p ∧ Nat.Prime p ∧ Nat.Prime q ∧ 2 * p < q ∧ 0 < r ∧ 0 < m ∧
      Function.support u = Metric.ball 0 r ∧
      Function.support v = Metric.ball (Real.log p) r ∧
      Function.support w = Metric.ball (Real.log q) r ∧
      ∀ (extra : ι → CCMArchimedeanFormDomain a) (x : Fin 3 ⊕ ι → ℝ),
        let f := ccmWeilTriangleExtension u.toCCMFormVector v.toCCMFormVector w.toCCMFormVector extra
        finiteSignedSeparateLower (fun i j => ccmWeilRealPolar a (f i) (f j)) x +
          m * (x (Sum.inl 0) ^ 2 + x (Sum.inl 1) ^ 2 + x (Sum.inl 2) ^ 2) /
            (6 * max 1 ((Fintype.card (Fin 3 ⊕ ι) : ℝ) - 2)) ≤
          ccmRestrictedWeilSourceQuadratic a (∑ i, (x i : ℂ) • f i) := by
  obtain ⟨p, q, r, _, a, u, v, w, hpN, hp, hq, hpq, hr, _, hus, hvs, hws, huv, huw, hvw, _⟩ :=
    exists_cofinal_ccmPrime_frustrated_triangle N
  let m := signedTriangleGain (ccmWeilRealPolar a u.toCCMFormVector v.toCCMFormVector)
    (ccmWeilRealPolar a u.toCCMFormVector w.toCCMFormVector)
    (ccmWeilRealPolar a v.toCCMFormVector w.toCCMFormVector)
  have hm : 0 < m := signedTriangleGain_pos_of_neg_neg_pos huv huw hvw
  exact ⟨p, q, r, m, a, u, v, w, hpN, hp, hq, hpq, hr, hm, hus, hvs, hws,
    fun extra x => ccmWeilTriangleExtension_lower a u.toCCMFormVector v.toCCMFormVector w.toCCMFormVector extra x⟩

end RHTower
