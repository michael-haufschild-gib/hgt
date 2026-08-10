import GaloisForLFunctions.HTGeometry.NewtonPuiseuxRoot

/-!
# Newton–Puiseux: the splitting form

Over an algebraically closed field of characteristic zero, a monic polynomial over `K⟦t⟧` does not
merely acquire *a* root after a ramification `t = s ^ N` — it splits completely into linear factors.

The upgrade is an induction on the degree.  One root is supplied by
`NewtonPuiseuxRoot.exists_isRoot_map_expand`; dividing it out leaves a monic polynomial of degree
one less, whose own ramification is composed with the first — ramifications compose because
`expand` does, `expand (N₂ N₁) = expand N₂ ∘ expand N₁`.

The conclusion is stated as an explicit product of linear factors rather than with
`Polynomial.Splits`, which needs the coefficient ring to be a field; `K⟦t⟧` is not.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial PowerSeries

variable {K : Type} [Field K]

/-- **Newton–Puiseux, splitting form.**  After a single ramification a monic polynomial over
`K⟦t⟧` factors into linear factors over `K⟦s⟧`. -/
theorem exists_prod_X_sub_C_map_expand [IsAlgClosed K] [CharZero K] (d : ℕ) :
    ∀ f : (PowerSeries K)[X], f.Monic → f.natDegree = d →
      ∃ (N : ℕ) (hN : N ≠ 0) (y : Fin d → PowerSeries K),
        f.map (PowerSeries.expand (R := K) N hN).toRingHom
          = ∏ i, (Polynomial.X - Polynomial.C (y i)) := by
  induction d with
  | zero =>
      intro f hf hdeg
      refine ⟨1, one_ne_zero, fun i => i.elim0, ?_⟩
      rw [Finset.univ_eq_empty, Finset.prod_empty]
      have hf1 : f = 1 := eq_one_of_monic_natDegree_zero hf hdeg
      rw [hf1, Polynomial.map_one]
  | succ d ih =>
      intro f hf hdeg
      -- one root, after a first ramification
      obtain ⟨N₁, hN₁, y₁, hy₁⟩ :=
        exists_isRoot_map_expand (K := K) (d + 1) f hf hdeg (by omega)
      obtain ⟨g, hg⟩ := (Polynomial.dvd_iff_isRoot (a := y₁)).2 hy₁
      have hfmonic : (f.map (PowerSeries.expand (R := K) N₁ hN₁).toRingHom).Monic := hf.map _
      have hlin : ((Polynomial.X : (PowerSeries K)[X]) - Polynomial.C y₁).Monic :=
        monic_X_sub_C y₁
      have hgmonic : g.Monic := hlin.of_mul_monic_left (hg ▸ hfmonic)
      have hgdeg : g.natDegree = d := by
        have hmul := hlin.natDegree_mul hgmonic
        rw [← hg, hf.natDegree_map, hdeg, Polynomial.natDegree_X_sub_C] at hmul
        omega
      -- the remaining factor splits after a second ramification
      obtain ⟨N₂, hN₂, y', hy'⟩ := ih g hgmonic hgdeg
      refine ⟨N₂ * N₁, Nat.mul_ne_zero hN₂ hN₁,
        Fin.cases ((PowerSeries.expand (R := K) N₂ hN₂) y₁) y', ?_⟩
      -- ramifications compose
      have hcomp : f.map (PowerSeries.expand (R := K) (N₂ * N₁) (Nat.mul_ne_zero hN₂ hN₁)).toRingHom
          = (f.map (PowerSeries.expand (R := K) N₁ hN₁).toRingHom).map
              (PowerSeries.expand (R := K) N₂ hN₂).toRingHom := by
        rw [Polynomial.map_map]
        congr 1
        refine RingHom.ext fun φ => ?_
        exact PowerSeries.expand_mul N₂ hN₂ N₁ hN₁ φ
      rw [hcomp, hg, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        hy', Fin.prod_univ_succ]
      simp

end GaloisForLFunctions.HTGeometry
