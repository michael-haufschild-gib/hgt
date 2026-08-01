import GaloisForLFunctions.HTGeometry.CompactAbelianTranslation
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# A finite-dimensional invariant subspace contains a character vector

If a nonzero finite-dimensional subspace of `L²(G)` is invariant under all translations, then it
contains a vector on which *every* translation acts by a scalar.

No spectral theory is needed for this: take an invariant subspace `V` of least dimension.  For each
`a` the translation `T a` has an eigenvalue on `V` (the ground field is algebraically closed and `V`
is finite-dimensional and nonzero), and the corresponding eigenspace is again invariant, because
translations commute.  Minimality forces that eigenspace to be all of `V`, so `T a` is a scalar on
`V` for every `a`.  Any nonzero vector of `V` is then a character vector.
-/

open MeasureTheory TopologicalSpace

namespace GaloisForLFunctions

namespace CompactAbelian

noncomputable section

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] in
/-- Translations compose. -/
theorem transOp_transOp (a b : G) (u : Lp ℂ 2 (haarProb G)) :
    transOp a (transOp b u) = transOp (a + b) u := by
  refine Lp.ext ?_
  have h1 := transOp_coeFn a (transOp b u)
  have h2 := (measurePreserving_translate (G := G) a).quasiMeasurePreserving.ae_eq_comp
      (transOp_coeFn b u)
  have h3 := transOp_coeFn (a + b) u
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  simp only [Function.comp_apply] at hx2
  rw [hx1, hx2, hx3]
  congr 1
  abel

omit [T2Space G] in
/-- Translations commute. -/
theorem transOp_comm (a b : G) (u : Lp ℂ 2 (haarProb G)) :
    transOp a (transOp b u) = transOp b (transOp a u) := by
  rw [transOp_transOp, transOp_transOp, add_comm]

omit [T2Space G] in
/-- **A nonzero finite-dimensional translation-invariant subspace contains a character vector.** -/
theorem exists_char_vector {W : Submodule ℂ (Lp ℂ 2 (haarProb G))}
    [FiniteDimensional ℂ W] (hWne : W ≠ ⊥)
    (hWinv : ∀ a : G, ∀ u ∈ W, transOp a u ∈ W) :
    ∃ (w : Lp ℂ 2 (haarProb G)) (χ : G → ℂ), w ≠ 0 ∧ w ∈ W ∧
      ∀ a : G, transOp a w = χ a • w := by
  classical
  set S : Set (Submodule ℂ (Lp ℂ 2 (haarProb G))) :=
    {V | V ≤ W ∧ V ≠ ⊥ ∧ ∀ a : G, ∀ u ∈ V, transOp a u ∈ V} with hS
  have hWS : W ∈ S := ⟨le_refl _, hWne, hWinv⟩
  -- every member of `S` is finite-dimensional
  have hfin : ∀ V ∈ S, FiniteDimensional ℂ V := fun V hV =>
    Submodule.finiteDimensional_of_le hV.1
  set N : Set ℕ := (fun V : Submodule ℂ (Lp ℂ 2 (haarProb G)) => Module.finrank ℂ V) '' S with hN
  have hNne : N.Nonempty := ⟨Module.finrank ℂ W, W, hWS, rfl⟩
  have hmem : sInf N ∈ N := Nat.sInf_mem hNne
  obtain ⟨V, hVS, hVrank⟩ := hmem
  have hVrank' : Module.finrank ℂ V = sInf N := hVrank
  haveI : FiniteDimensional ℂ V := hfin V hVS
  obtain ⟨hVW, hVne, hVinv⟩ := hVS
  haveI : Nontrivial V := by
    rw [Submodule.nontrivial_iff_ne_bot]
    exact hVne
  -- every translation is a scalar on `V`
  have hscalar : ∀ a : G, ∃ c : ℂ, ∀ u ∈ V, transOp a u = c • u := by
    intro a
    set R : V →ₗ[ℂ] V := LinearMap.restrict (transOp a).toLinearMap (hVinv a) with hR
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue R
    refine ⟨c, ?_⟩
    -- the eigenspace, viewed inside the big space
    set E : Submodule ℂ (Lp ℂ 2 (haarProb G)) :=
      Submodule.map V.subtype (Module.End.eigenspace R c) with hE
    have hEle : E ≤ V := by
      rintro x ⟨y, -, rfl⟩
      exact y.2
    have hEne : E ≠ ⊥ := by
      intro hbot
      have hzero : Module.End.eigenspace R c = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        have : (y : Lp ℂ 2 (haarProb G)) ∈ E := ⟨y, hy, rfl⟩
        rw [hbot, Submodule.mem_bot] at this
        rw [Submodule.mem_bot]
        exact Subtype.ext this
      exact hc hzero
    have hEinv : ∀ b : G, ∀ u ∈ E, transOp b u ∈ E := by
      rintro b x ⟨y, hy, rfl⟩
      have hy' : y ∈ Module.End.eigenspace R c := hy
      have hyeig : R y = c • y := Module.End.mem_eigenspace_iff.mp hy'
      have hyV : transOp b (y : Lp ℂ 2 (haarProb G)) ∈ V := hVinv b y y.2
      have hmem : (⟨transOp b (y : Lp ℂ 2 (haarProb G)), hyV⟩ : V)
          ∈ Module.End.eigenspace R c := by
        rw [Module.End.mem_eigenspace_iff]
        apply Subtype.ext
        have hRb : ((R ⟨transOp b (y : Lp ℂ 2 (haarProb G)), hyV⟩ : V) : Lp ℂ 2 (haarProb G))
            = transOp a (transOp b (y : Lp ℂ 2 (haarProb G))) := rfl
        have hRy : ((R y : V) : Lp ℂ 2 (haarProb G)) = transOp a (y : Lp ℂ 2 (haarProb G)) := rfl
        rw [hRb, transOp_comm, ← hRy, hyeig]
        simp
      exact ⟨_, hmem, rfl⟩
    have hES : E ∈ S := ⟨le_trans hEle hVW, hEne, hEinv⟩
    have hrank : Module.finrank ℂ V ≤ Module.finrank ℂ E := by
      rw [hVrank']
      exact Nat.sInf_le ⟨E, hES, rfl⟩
    have hEV : E = V := Submodule.eq_of_le_of_finrank_le hEle hrank
    intro u hu
    have huE : u ∈ E := by rw [hEV]; exact hu
    obtain ⟨y, hy, rfl⟩ := huE
    have hy' : y ∈ Module.End.eigenspace R c := hy
    have hyeig : R y = c • y := Module.End.mem_eigenspace_iff.mp hy'
    show transOp a (y : Lp ℂ 2 (haarProb G)) = c • (y : Lp ℂ 2 (haarProb G))
    have hRy : ((R y : V) : Lp ℂ 2 (haarProb G)) = transOp a (y : Lp ℂ 2 (haarProb G)) := rfl
    rw [← hRy, hyeig]
    rfl
  choose χ hχ using hscalar
  obtain ⟨w, hwV, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
  exact ⟨w, χ, hw0, hVW hwV, fun a => hχ a w hwV⟩

end

end CompactAbelian

end GaloisForLFunctions
