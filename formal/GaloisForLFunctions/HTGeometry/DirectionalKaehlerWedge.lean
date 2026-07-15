import GaloisForLFunctions.HTGeometry.DirectionalJetWordPolynomial
import GaloisForLFunctions.HTGeometry.KaehlerAlgebraicIndependence
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Finite directional Kähler wedges

The top exterior product of a finite family over a field vanishes exactly when the family is
linearly dependent.  Applied to universal Kähler differentials, this turns finite directional
jet dependence into an explicit exterior-power equation.  The finite equations are nested, and
their countable union is exactly failure of algebraic independence of the full directional jet.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Module Set

/-- A linearly independent finite family has nonzero top exterior product. -/
theorem exteriorPower_ιMulti_ne_zero_of_linearIndependent
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {n : ℕ} (v : Fin n → M) (hv : LinearIndependent K v) :
    exteriorPower.ιMulti K n v ≠ 0 := by
  let s : Set.powersetCard (Fin n) n :=
    Set.powersetCard.ofFinEmbEquiv (OrderEmbedding.id (Fin n))
  have hLI := exteriorPower.ιMulti_family_linearIndependent_field (n := n) hv
  have hne := hLI.ne_zero s
  simpa [exteriorPower.ιMulti_family, s] using hne

/-- A linearly dependent finite family has zero top exterior product.  This direction is proved by
passing to the finite-dimensional span: its dimension is strictly below the family cardinality,
so its top exterior power is the zero module. -/
theorem exteriorPower_ιMulti_eq_zero_of_not_linearIndependent
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {n : ℕ} (v : Fin n → M) (hv : ¬ LinearIndependent K v) :
    exteriorPower.ιMulti K n v = 0 := by
  let W : Submodule K M := Submodule.span K (Set.range v)
  let w : Fin n → W := fun i => ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩
  letI : Module.Finite K W := by
    dsimp [W]
    exact FiniteDimensional.span_of_finite K (Set.finite_range v)
  have hdim_le : Module.finrank K W ≤ n := by
    simpa [W] using (finrank_range_le_card (R := K) v)
  have hdim_ne : Module.finrank K W ≠ n := by
    intro h
    apply hv
    apply (linearIndependent_iff_card_eq_finrank_span (R := K)).2
    simpa [W] using h.symm
  have hdim_lt : Module.finrank K W < n := lt_of_le_of_ne hdim_le hdim_ne
  have hfin : Module.finrank K (⋀[K]^n W) = 0 := by
    rw [exteriorPower.finrank_eq, Nat.choose_eq_zero_of_lt hdim_lt]
  letI : Subsingleton (⋀[K]^n W) := Module.finrank_zero_iff.mp hfin
  have hwedge : exteriorPower.ιMulti K n w = 0 := Subsingleton.elim _ _
  have hmap := congrArg (exteriorPower.map n W.subtype) hwedge
  simpa [w, Function.comp_def] using hmap

/-- Exact finite-dimensional wedge criterion over a field. -/
theorem exteriorPower_ιMulti_eq_zero_iff_not_linearIndependent
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {n : ℕ} (v : Fin n → M) :
    exteriorPower.ιMulti K n v = 0 ↔ ¬ LinearIndependent K v := by
  constructor
  · intro hzero hLI
    exact (exteriorPower_ιMulti_ne_zero_of_linearIndependent v hLI) hzero
  · exact exteriorPower_ιMulti_eq_zero_of_not_linearIndependent v

/-- Algebraic independence of a sequence is equivalent to algebraic independence of every
nonempty initial segment. -/
theorem algebraicIndependent_nat_iff_initialSegments
    {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (x : ℕ → A) :
    AlgebraicIndependent K x ↔
      ∀ n, AlgebraicIndependent K (fun j : Fin (n + 1) => x j) := by
  constructor
  · intro hx n
    exact hx.comp (fun j : Fin (n + 1) => (j : ℕ)) Fin.val_injective
  · intro h
    apply algebraicIndependent_of_finite_type
    intro s hs
    rcases hs.bddAbove with ⟨N, hN⟩
    let e : s → Fin (N + 1) := fun i => ⟨i.1, Nat.lt_succ_of_le (hN i.2)⟩
    have he : Function.Injective e := by
      intro i j hij
      apply Subtype.ext
      exact Fin.ext_iff.mp hij
    have hsub := (h N).comp e he
    simpa [e, Function.comp_def] using hsub

variable {k K L ι : Type*} [Field k] [Field K] [Field L]
  [Algebra k L] [Algebra K L] [CharZero K] [Fintype ι]

/-- The universal Kähler wedge of the first `n + 1` jets along a direction. -/
def directionalKaehlerWedge
    (δ : ι → Derivation k L L) (c : ι → k) (x : L) (n : ℕ) :
    ⋀[L]^(n + 1) Ω[L⁄K] :=
  exteriorPower.ιMulti L (n + 1)
    (fun j : Fin (n + 1) =>
      KaehlerDifferential.D K L (directionalJet δ c j x))

/-- The finite directional Kähler equation is exactly algebraic dependence of that initial jet
segment; no dependence or rank hypothesis is assumed. -/
theorem directionalKaehlerWedge_eq_zero_iff_not_algebraicIndependent
    (δ : ι → Derivation k L L) (c : ι → k) (x : L) (n : ℕ) :
    directionalKaehlerWedge (K := K) δ c x n = 0 ↔
      ¬ AlgebraicIndependent K
        (fun j : Fin (n + 1) => directionalJet δ c j x) := by
  rw [directionalKaehlerWedge,
    exteriorPower_ιMulti_eq_zero_iff_not_linearIndependent]
  exact not_congr (algebraicIndependent_iff_kaehlerD_linearIndependent _).symm

/-- Finite directional dependence persists after adjoining the next jet. -/
theorem directionalKaehlerWedge_zero_mono
    (δ : ι → Derivation k L L) (c : ι → k) (x : L) {n : ℕ}
    (hzero : directionalKaehlerWedge (K := K) δ c x n = 0) :
    directionalKaehlerWedge (K := K) δ c x (n + 1) = 0 := by
  rw [directionalKaehlerWedge_eq_zero_iff_not_algebraicIndependent] at hzero ⊢
  intro hbig
  apply hzero
  have hsub := hbig.comp Fin.castSucc (Fin.castSucc_injective _)
  simpa [Function.comp_def] using hsub

/-- The countable union of finite Kähler loci is exactly failure of algebraic independence of the
complete directional jet tower. -/
theorem directionalJet_not_algebraicIndependent_iff_exists_kaehlerWedge_zero
    (δ : ι → Derivation k L L) (c : ι → k) (x : L) :
    (¬ AlgebraicIndependent K (fun n : ℕ => directionalJet δ c n x)) ↔
      ∃ n, directionalKaehlerWedge (K := K) δ c x n = 0 := by
  rw [algebraicIndependent_nat_iff_initialSegments]
  push Not
  apply exists_congr
  intro n
  exact (directionalKaehlerWedge_eq_zero_iff_not_algebraicIndependent δ c x n).symm

end

end GaloisForLFunctions.HTGeometry
