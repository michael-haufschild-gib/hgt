import GaloisForLFunctions.Core
import Mathlib.Analysis.Meromorphic.TrailingCoefficient

/-!
# A pole-support obstruction for meromorphic translation coboundaries

A finitely supported pole pattern on an integer translation orbit has two boundary points.  At the
first boundary, the translated function has a pole while the original function is regular; at the
last boundary the roles reverse.  Meromorphic order therefore proves that a shift coboundary
cannot have exactly one pole on that orbit.  No Laurent-coefficient extractor is required.
-/

open Filter Topology Set Function

namespace GaloisForLFunctions

noncomputable section

/-- The point with integer coordinate `n` on the additive `q`-orbit based at `p`. -/
def additiveOrbitPoint (p q : ℂ) (n : ℤ) : ℂ := p + n * q

/-- The integer indices at which a meromorphic function has a pole on one additive orbit. -/
def poleIndexSet (g : ℂ → ℂ) (p q : ℂ) : Set ℤ :=
  {n | meromorphicOrderAt g (additiveOrbitPoint p q n) < 0}

theorem meromorphicAt_comp_add_const_of_orbit
    {g : ℂ → ℂ} {p q : ℂ}
    (hg : MeromorphicAt g (additiveOrbitPoint p q 1)) :
    MeromorphicAt (fun z => g (z + q)) p := by
  have hg' : MeromorphicAt g (p + q) := by simpa [additiveOrbitPoint] using hg
  change MeromorphicAt (g ∘ fun z : ℂ => z + q) p
  have hinner : AnalyticAt ℂ (fun z : ℂ => z + q) p := by fun_prop
  exact MeromorphicAt.comp_analyticAt (x := p) (f := g)
    (g := fun z : ℂ => z + q) hg' hinner

theorem additiveOrbitPoint_add (p q : ℂ) (n : ℤ) :
    additiveOrbitPoint p q n + q = additiveOrbitPoint p q (n + 1) := by
  simp [additiveOrbitPoint]
  ring

theorem meromorphicAt_shift_at_orbit
    {g : ℂ → ℂ} {p q : ℂ} (n : ℤ)
    (hg : MeromorphicAt g (additiveOrbitPoint p q (n + 1))) :
    MeromorphicAt (fun z => g (z + q)) (additiveOrbitPoint p q n) := by
  have hinner : AnalyticAt ℂ (fun z : ℂ => z + q) (additiveOrbitPoint p q n) := by
    fun_prop
  apply MeromorphicAt.comp_analyticAt (x := additiveOrbitPoint p q n) (f := g)
    (g := fun z : ℂ => z + q) _ hinner
  simpa only [additiveOrbitPoint_add] using hg

theorem meromorphicOrderAt_shift_at_orbit
    (g : ℂ → ℂ) (p q : ℂ) (n : ℤ) :
    meromorphicOrderAt (fun z => g (z + q)) (additiveOrbitPoint p q n) =
      meromorphicOrderAt g (additiveOrbitPoint p q (n + 1)) := by
  change meromorphicOrderAt (g ∘ fun z : ℂ => z + q) (additiveOrbitPoint p q n) = _
  rw [meromorphicOrderAt_comp_of_deriv_ne_zero (f := g)
    (g := fun z : ℂ => z + q) (x := additiveOrbitPoint p q n) (by fun_prop) (by simp)]
  congr 1
  exact additiveOrbitPoint_add p q n

/-- **Pole-support boundary obstruction.** If the pole indices of `g` on one translation orbit are
finite, then its shift coboundary `g(z+q)-g(z)` cannot have exactly one pole on that orbit. -/
theorem shiftCoboundary_not_singleton_poleOrbit
    (g f : ℂ → ℂ) (p q : ℂ)
    (hg : ∀ n : ℤ, MeromorphicAt g (additiveOrbitPoint p q n))
    (hfg : ∀ z : ℂ, f z = g (z + q) - g z)
    (hfinite : (poleIndexSet g p q).Finite)
    (hfpole : meromorphicOrderAt f p < 0)
    (hunique : ∀ n : ℤ,
      meromorphicOrderAt f (additiveOrbitPoint p q n) < 0 → n = 0) : False := by
  classical
  have hSnonempty : (poleIndexSet g p q).Nonempty := by
    by_contra hS
    rw [Set.not_nonempty_iff_eq_empty] at hS
    have h0reg : 0 ≤ meromorphicOrderAt g p := by
      have h0not : (0 : ℤ) ∉ poleIndexSet g p q := by simp [hS]
      have h0not' : ¬ meromorphicOrderAt g p < 0 := by
        simpa [poleIndexSet, additiveOrbitPoint] using h0not
      exact not_lt.mp h0not'
    have h1reg : 0 ≤ meromorphicOrderAt g (p + q) := by
      have h1not : (1 : ℤ) ∉ poleIndexSet g p q := by simp [hS]
      have h1not' : ¬ meromorphicOrderAt g (p + q) < 0 := by
        simpa [poleIndexSet, additiveOrbitPoint] using h1not
      exact not_lt.mp h1not'
    have hgshift : MeromorphicAt (fun z => g (z + q)) p :=
      meromorphicAt_comp_add_const_of_orbit (by simpa [additiveOrbitPoint] using hg 1)
    have hg0 : MeromorphicAt g p := by simpa [additiveOrbitPoint] using hg 0
    have hsub := meromorphicOrderAt_add hgshift hg0.neg
    have horderShift : meromorphicOrderAt (fun z => g (z + q)) p =
        meromorphicOrderAt g (p + q) := by
      change meromorphicOrderAt (g ∘ fun z : ℂ => z + q) p = _
      exact meromorphicOrderAt_comp_of_deriv_ne_zero (f := g)
        (g := fun z : ℂ => z + q) (x := p) (by fun_prop) (by simp)
    have hmin : 0 ≤ min (meromorphicOrderAt (fun z => g (z + q)) p)
        (meromorphicOrderAt (-g) p) := by
      refine le_min ?_ ?_
      · rwa [horderShift]
      · rwa [← meromorphicOrderAt_neg (f := g) (x := p)]
    have hnonpole : 0 ≤ meromorphicOrderAt (fun z => g (z + q) - g z) p :=
      hmin.trans hsub
    have heq : f = fun z => g (z + q) - g z := funext hfg
    rw [heq] at hfpole
    exact (not_lt_of_ge hnonpole) hfpole
  let S : Finset ℤ := hfinite.toFinset
  have hSne : S.Nonempty := by
    simpa [S] using hSnonempty
  let a : ℤ := S.min' hSne
  let b : ℤ := S.max' hSne
  have haS : a ∈ poleIndexSet g p q := by
    have : a ∈ S := Finset.min'_mem S hSne
    simpa [S] using this
  have hbS : b ∈ poleIndexSet g p q := by
    have : b ∈ S := Finset.max'_mem S hSne
    simpa [S] using this
  have haPredNot : a - 1 ∉ poleIndexSet g p q := by
    intro ha
    have haFin : a - 1 ∈ S := by simpa [S] using ha
    have hle := Finset.min'_le S (a - 1) haFin
    omega
  have hbSuccNot : b + 1 ∉ poleIndexSet g p q := by
    intro hb
    have hbFin : b + 1 ∈ S := by simpa [S] using hb
    have hle := Finset.le_max' S (b + 1) hbFin
    omega
  have haPole : meromorphicOrderAt g (additiveOrbitPoint p q a) < 0 := by
    simpa [poleIndexSet] using haS
  have haPredReg : 0 ≤ meromorphicOrderAt g (additiveOrbitPoint p q (a - 1)) := by
    have hnot : ¬ meromorphicOrderAt g (additiveOrbitPoint p q (a - 1)) < 0 := by
      simpa [poleIndexSet] using haPredNot
    exact not_lt.mp hnot
  have hbPole : meromorphicOrderAt g (additiveOrbitPoint p q b) < 0 := by
    simpa [poleIndexSet] using hbS
  have hbSuccReg : 0 ≤ meromorphicOrderAt g (additiveOrbitPoint p q (b + 1)) := by
    have hnot : ¬ meromorphicOrderAt g (additiveOrbitPoint p q (b + 1)) < 0 := by
      simpa [poleIndexSet] using hbSuccNot
    exact not_lt.mp hnot
  have hfun : f = fun z => g (z + q) - g z := funext hfg
  have haBoundaryPole :
      meromorphicOrderAt f (additiveOrbitPoint p q (a - 1)) < 0 := by
    let x := additiveOrbitPoint p q (a - 1)
    have hshiftM : MeromorphicAt (fun z => g (z + q)) x := by
      apply meromorphicAt_shift_at_orbit (n := a - 1)
      convert hg a using 2
      omega
    have hgPredM : MeromorphicAt g x := hg (a - 1)
    have hshiftOrder : meromorphicOrderAt (fun z => g (z + q)) x =
        meromorphicOrderAt g (additiveOrbitPoint p q a) := by
      rw [meromorphicOrderAt_shift_at_orbit]
      congr 2
      omega
    have hnegOrder : meromorphicOrderAt (-g) x = meromorphicOrderAt g x := by
      exact (meromorphicOrderAt_neg (f := g) (x := x)).symm
    have hlt : meromorphicOrderAt (fun z => g (z + q)) x <
        meromorphicOrderAt (-g) x := by
      rw [hshiftOrder, hnegOrder]
      exact haPole.trans_le haPredReg
    have horder := meromorphicOrderAt_add_eq_left_of_lt hgPredM.neg hlt
    rw [hfun]
    change meromorphicOrderAt ((fun z => g (z + q)) + (-g)) x < 0
    rw [horder, hshiftOrder]
    exact haPole
  have hbBoundaryPole :
      meromorphicOrderAt f (additiveOrbitPoint p q b) < 0 := by
    let x := additiveOrbitPoint p q b
    have hshiftM : MeromorphicAt (fun z => g (z + q)) x := by
      exact meromorphicAt_shift_at_orbit b (hg (b + 1))
    have hgBM : MeromorphicAt g x := hg b
    have hshiftOrder : meromorphicOrderAt (fun z => g (z + q)) x =
        meromorphicOrderAt g (additiveOrbitPoint p q (b + 1)) :=
      meromorphicOrderAt_shift_at_orbit g p q b
    have hnegOrder : meromorphicOrderAt (-g) x = meromorphicOrderAt g x := by
      exact (meromorphicOrderAt_neg (f := g) (x := x)).symm
    have hlt : meromorphicOrderAt (-g) x <
        meromorphicOrderAt (fun z => g (z + q)) x := by
      rw [hshiftOrder, hnegOrder]
      exact hbPole.trans_le hbSuccReg
    have horder := meromorphicOrderAt_add_eq_right_of_lt hshiftM hlt
    rw [hfun]
    change meromorphicOrderAt ((fun z => g (z + q)) + (-g)) x < 0
    rw [horder, hnegOrder]
    exact hbPole
  have ha0 := hunique (a - 1) haBoundaryPole
  have hb0 := hunique b hbBoundaryPole
  have hab : a ≤ b := Finset.min'_le _ _ (Finset.max'_mem S hSne)
  omega

end

end GaloisForLFunctions
