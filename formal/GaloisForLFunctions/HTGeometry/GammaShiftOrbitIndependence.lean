import GaloisForLFunctions.HTGeometry.MeromorphicPoleOrbitBoundary
import GaloisForLFunctions.HTGeometry.MeromorphicSimplePoleDifferentialOperator

/-!
# Incongruent shifted simple poles admit no differential shift coboundary

The additive difference equation of the shifted digamma is `ψ(s+λ+1) − ψ(s+λ) = 1/(s+λ)`.  A
differential relation among finitely many shifted digammas produces a nonzero constant-coefficient
linear differential polynomial `P` and a meromorphic `g` with finitely many poles on one translation
orbit such that

```text
∑ᵢ Lᵢ(∂)(1/(s+λᵢ)) = g(s+1) − g(s).
```

Pairwise incongruent shifts put the poles of the left side on pairwise distinct translation orbits,
one pole on each.  A shift coboundary cannot have exactly one pole on an orbit — its pole indices on
an orbit come in a nonempty finite set whose extremes both survive — so the identity forces every
`Lᵢ` to vanish.

This is the orbit-residue core of the shifted-Gamma independence theorem, with the analytic input
`ψ` replaced by the exact simple poles its difference equation produces.
-/

open Filter Topology Set Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The simple pole `1/(z+λ)` at `-λ`. -/
def shiftedInv (lam : ℂ) : ℂ → ℂ := fun z => (z + lam)⁻¹

/-- A finite constant-coefficient linear differential polynomial evaluated on the shifted simple
poles. -/
def shiftedInvOperatorSum {r : ℕ} (L : Fin r → Polynomial ℂ) (lam : Fin r → ℂ) : ℂ → ℂ :=
  fun z => ∑ i : Fin r, constantCoeffDifferentialOperator (L i) (shiftedInv (lam i)) z

theorem meromorphicAt_shiftedInv (lam p : ℂ) : MeromorphicAt (shiftedInv lam) p := by
  unfold shiftedInv
  fun_prop

theorem analyticAt_shiftedInv {lam p : ℂ} (h : p + lam ≠ 0) :
    AnalyticAt ℂ (shiftedInv lam) p := by
  unfold shiftedInv
  exact (analyticAt_id.add analyticAt_const).inv h

/-- The order of the shifted simple pole at its pole is `-1`. -/
theorem meromorphicOrderAt_shiftedInv (lam : ℂ) :
    meromorphicOrderAt (shiftedInv lam) (-lam) = ((-1 : ℤ) : WithTop ℤ) := by
  have hbase := meromorphicOrderAt_zpow_id_sub_const (𝕜 := ℂ) (x := -lam) (n := (-1 : ℤ))
  have hfun : ((fun z : ℂ => z - (-lam)) ^ (-1 : ℤ)) = shiftedInv lam := by
    funext z
    simp [shiftedInv, sub_neg_eq_add]
  rw [hfun] at hbase
  exact hbase

/-- Away from its pole the shifted simple pole is analytic, hence so is any constant-coefficient
differential operator applied to it. -/
theorem analyticAt_shiftedInvOperator {L : Polynomial ℂ} {lam p : ℂ} (h : p + lam ≠ 0) :
    AnalyticAt ℂ (constantCoeffDifferentialOperator L (shiftedInv lam)) p :=
  analyticAt_constantCoeffDifferentialOperator (analyticAt_shiftedInv h)

/-- Off the poles of every member, the whole differential combination is analytic. -/
theorem analyticAt_shiftedInvOperatorSum {r : ℕ} (L : Fin r → Polynomial ℂ) (lam : Fin r → ℂ)
    {p : ℂ} (h : ∀ i, p + lam i ≠ 0) :
    AnalyticAt ℂ (shiftedInvOperatorSum L lam) p := by
  unfold shiftedInvOperatorSum
  exact Finset.analyticAt_fun_sum _ fun i _ => analyticAt_shiftedInvOperator (h i)

/-- **The pole order of the combination at one of its poles.**  Only the member sitting at that
point contributes, and its order is the degree of its symbol shifted by one. -/
theorem meromorphicOrderAt_shiftedInvOperatorSum {r : ℕ} (L : Fin r → Polynomial ℂ)
    (lam : Fin r → ℂ) (i₀ : Fin r) (hL : L i₀ ≠ 0)
    (hdist : ∀ i, i ≠ i₀ → lam i ≠ lam i₀) :
    meromorphicOrderAt (shiftedInvOperatorSum L lam) (-lam i₀)
      = ((-(((L i₀).natDegree + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  classical
  set F : Fin r → ℂ → ℂ :=
    fun i => constantCoeffDifferentialOperator (L i) (shiftedInv (lam i)) with hF
  set G : ℂ → ℂ := fun z => ∑ i ∈ Finset.univ.erase i₀, F i z with hG
  have hsplit : shiftedInvOperatorSum L lam = F i₀ + G := by
    funext z
    show (∑ i : Fin r, F i z) = F i₀ z + ∑ i ∈ Finset.univ.erase i₀, F i z
    exact (Finset.add_sum_erase Finset.univ (fun i => F i z) (Finset.mem_univ i₀)).symm
  have hGanalytic : AnalyticAt ℂ G (-lam i₀) := by
    refine Finset.analyticAt_fun_sum _ fun i hi => ?_
    have hne : lam i ≠ lam i₀ := hdist i (Finset.mem_erase.mp hi).1
    refine analyticAt_shiftedInvOperator ?_
    intro h0
    exact hne (by linear_combination h0)
  have hpole : meromorphicOrderAt (F i₀) (-lam i₀)
      = ((-(((L i₀).natDegree + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) :=
    meromorphicOrderAt_constantCoeffDifferentialOperator_of_simplePole hL
      (meromorphicAt_shiftedInv _ _) (meromorphicOrderAt_shiftedInv _)
  have hlt : meromorphicOrderAt (F i₀) (-lam i₀) < meromorphicOrderAt G (-lam i₀) := by
    refine lt_of_lt_of_le ?_ hGanalytic.meromorphicOrderAt_nonneg
    rw [hpole]
    exact_mod_cast (show -(((L i₀).natDegree + 1 : ℕ) : ℤ) < 0 by omega)
  rw [hsplit, meromorphicOrderAt_add_eq_left_of_lt hGanalytic.meromorphicAt hlt, hpole]

/-- **The orbit-residue obstruction.**  With pairwise incongruent shifts, a nonzero
constant-coefficient differential combination of the shifted simple poles is not the shift
coboundary of any meromorphic function with finite pole support on the orbit of the pole. -/
theorem no_shiftCoboundary_shiftedInvOperatorSum {r : ℕ} (L : Fin r → Polynomial ℂ)
    (lam : Fin r → ℂ) (hincong : ∀ i j, i ≠ j → ∀ m : ℤ, lam i - lam j ≠ (m : ℂ))
    (i₀ : Fin r) (hL : L i₀ ≠ 0) (g : ℂ → ℂ)
    (hg : ∀ n : ℤ, MeromorphicAt g (additiveOrbitPoint (-lam i₀) 1 n))
    (hfinite : (poleIndexSet g (-lam i₀) 1).Finite)
    (hshift : ∀ z : ℂ, shiftedInvOperatorSum L lam z = g (z + 1) - g z) : False := by
  classical
  have hdist : ∀ i, i ≠ i₀ → lam i ≠ lam i₀ := by
    intro i hi h0
    have := hincong i i₀ hi 0
    rw [h0] at this
    simp at this
  have horbit : ∀ n : ℤ, additiveOrbitPoint (-lam i₀) 1 n = -lam i₀ + (n : ℂ) := by
    intro n
    simp [additiveOrbitPoint]
  refine shiftCoboundary_not_singleton_poleOrbit g (shiftedInvOperatorSum L lam) (-lam i₀) 1
    hg hshift hfinite ?_ ?_
  · rw [meromorphicOrderAt_shiftedInvOperatorSum L lam i₀ hL hdist]
    exact_mod_cast (show -(((L i₀).natDegree + 1 : ℕ) : ℤ) < 0 by omega)
  · intro n hn
    by_contra hn0
    have hanalytic : AnalyticAt ℂ (shiftedInvOperatorSum L lam)
        (additiveOrbitPoint (-lam i₀) 1 n) := by
      rw [horbit n]
      refine analyticAt_shiftedInvOperatorSum L lam fun i => ?_
      intro h0
      by_cases hi : i = i₀
      · subst hi
        have : (n : ℂ) = 0 := by linear_combination h0
        exact hn0 (by exact_mod_cast this)
      · exact hincong i i₀ hi (-n) (by push_cast; linear_combination h0)
    exact (not_lt_of_ge hanalytic.meromorphicOrderAt_nonneg) hn

/-- A polynomial is analytic. -/
theorem analyticAt_polyEval (A : Polynomial ℂ) (p : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => A.eval z) p := by
  simpa using (analyticAt_id : AnalyticAt ℂ (fun y : ℂ => y) p).aeval_polynomial A

/-- The pole indices of a rational function on a translation orbit are finite. -/
theorem poleIndexSet_finite_ratio (A B : Polynomial ℂ) (hB : B ≠ 0) (p q : ℂ) (hq : q ≠ 0) :
    (poleIndexSet (fun z => A.eval z / B.eval z) p q).Finite := by
  classical
  have hsub : poleIndexSet (fun z => A.eval z / B.eval z) p q
      ⊆ (fun n : ℤ => additiveOrbitPoint p q n) ⁻¹' {z : ℂ | B.IsRoot z} := by
    intro n hn
    by_contra hroot
    have hne : B.eval (additiveOrbitPoint p q n) ≠ 0 := hroot
    have hanalytic : AnalyticAt ℂ (fun z => A.eval z / B.eval z)
        (additiveOrbitPoint p q n) :=
      (analyticAt_polyEval A _).div (analyticAt_polyEval B _) hne
    exact (not_lt_of_ge hanalytic.meromorphicOrderAt_nonneg) hn
  refine Set.Finite.subset (Set.Finite.preimage ?_ (Polynomial.finite_setOf_isRoot hB)) hsub
  intro m _ n _ hmn
  have : (m : ℂ) * q = (n : ℂ) * q := by
    simp only [additiveOrbitPoint] at hmn
    linear_combination hmn
  have hmn' : (m : ℂ) = (n : ℂ) := mul_right_cancel₀ hq this
  exact_mod_cast hmn'

/-- **Equation (8).**  For pairwise incongruent real shifts no nonzero constant-coefficient linear
differential polynomial in the shifted simple poles is the shift coboundary of a rational function.
This is the residue calculation behind the differential independence of the shifted digammas. -/
theorem shiftedInv_no_constantCoeff_rational_coboundary {r : ℕ} (lam : Fin r → ℝ)
    (hincong : ∀ i j, i ≠ j → ∀ m : ℤ, lam i - lam j ≠ (m : ℝ))
    (L : Fin r → Polynomial ℂ) (i₀ : Fin r) (hL : L i₀ ≠ 0)
    (A B : Polynomial ℂ) (hB : B ≠ 0)
    (hshift : ∀ z : ℂ, shiftedInvOperatorSum L (fun i => ((lam i : ℝ) : ℂ)) z
      = A.eval (z + 1) / B.eval (z + 1) - A.eval z / B.eval z) : False := by
  classical
  have hincongC : ∀ i j, i ≠ j → ∀ m : ℤ,
      ((lam i : ℝ) : ℂ) - ((lam j : ℝ) : ℂ) ≠ (m : ℂ) := by
    intro i j hij m h
    exact hincong i j hij m (by exact_mod_cast h)
  set p : ℂ := -((lam i₀ : ℝ) : ℂ) with hp
  refine no_shiftCoboundary_shiftedInvOperatorSum L (fun i => ((lam i : ℝ) : ℂ)) hincongC i₀ hL
    (fun z => A.eval z / B.eval z) (fun n => ?_) ?_ hshift
  · exact ((analyticAt_polyEval A _).meromorphicAt).div ((analyticAt_polyEval B _).meromorphicAt)
  · exact poleIndexSet_finite_ratio A B hB p 1 one_ne_zero

end

end GaloisForLFunctions.HTGeometry
