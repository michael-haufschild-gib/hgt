import GaloisForLFunctions.HTGeometry.HLSBrackets
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The orthonormal supercharge basis

Positivity of the odd sector makes the coefficient form of `{Q, Q̄}` a positive definite
Hermitian form on the undotted highest-weight sector.  Diagonalizing it produces the
`N` supercharges `Q^(1 : ℕ), …, Q^N` for which the Haag--Łopuszański--Sohnius relation takes its
standard normalized shape

  `{Q^I_α, Q̄^J_β̇} = 2 δ^{IJ} P_{α β̇}`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

/-- Existence of an orthonormal basis for a positive definite Hermitian sesquilinear form
on a finite-dimensional complex vector space. -/
theorem hlsExistsOrthonormal {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (f : W → W → ℂ)
    (hadd : ∀ u v w, f (u + v) w = f u w + f v w)
    (hsmul : ∀ (c : ℂ) (u v : W), f (c • u) v = c * f u v)
    (hherm : ∀ u v, (starRingEnd ℂ) (f v u) = f u v)
    (hpos : ∀ u : W, u ≠ 0 → 0 < (f u u).re) :
    ∃ (n : ℕ) (e : Fin n → W), (∀ i j, f (e i) (e j) = if i = j then 1 else 0) ∧
      Submodule.span ℂ (Set.range e) = ⊤ := by
  classical
  letI core : InnerProductSpace.Core ℂ W :=
    { inner := fun u v => f v u
      conj_inner_symm := fun x y => hherm y x
      re_inner_nonneg := fun x => by
        rcases eq_or_ne x 0 with rfl | hx
        · have h0 : f (0 : W) (0 : W) = 0 := by
            have := hsmul 0 (0 : W) (0 : W)
            simpa using this
          simp [h0]
        · exact le_of_lt (hpos x hx)
      add_left := fun x y z => by
        show f z (x + y) = f z x + f z y
        have h1 : f z (x + y) = (starRingEnd ℂ) (f (x + y) z) := by
          rw [← hherm (x + y) z]; simp
        have h2 : f z x = (starRingEnd ℂ) (f x z) := by rw [← hherm x z]; simp
        have h3 : f z y = (starRingEnd ℂ) (f y z) := by rw [← hherm y z]; simp
        rw [h1, h2, h3, hadd, map_add]
      smul_left := fun x y r => by
        show f y (r • x) = (starRingEnd ℂ) r * f y x
        have h1 : f y (r • x) = (starRingEnd ℂ) (f (r • x) y) := by
          rw [← hherm (r • x) y]; simp
        have h2 : f y x = (starRingEnd ℂ) (f x y) := by rw [← hherm x y]; simp
        rw [h1, h2, hsmul, map_mul]
      definite := fun x hx => by
        by_contra hne
        have hp := hpos x hne
        have hxx : f x x = 0 := hx
        rw [hxx] at hp
        simp at hp }
  letI : NormedAddCommGroup W := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ W := InnerProductSpace.ofCore core.toCore
  let b := stdOrthonormalBasis ℂ W
  refine ⟨Module.finrank ℂ W, fun i => b i, ?_, ?_⟩
  · intro i j
    have h := (orthonormal_iff_ite (𝕜 := ℂ)).mp b.orthonormal j i
    show f (b i) (b j) = _
    have hb : (inner ℂ (b j) (b i) : ℂ) = f (b i) (b j) := rfl
    rw [← hb, h]
    by_cases hij : i = j <;> simp [hij, eq_comm]
  · simpa using b.toBasis.span_eq

namespace HLSGradedSymmetry

variable {B : Type*} [LieRing B] [LieAlgebra ℂ B]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (S : HLSGradedSymmetry B V)

/-- Coefficient of the mixed bracket `{Q, Q̄}` along `P_{1 1̇}`. -/
def hlsBeta (u v : V) : ℂ := (S.br u (S.oddConj v)).2.2.1 0 0

variable [FiniteDimensional ℂ V]

theorem br_pos_beta {u v : V} (hu : u ∈ S.wt 1 0) (hv : v ∈ S.wt 1 0) :
    S.br u (S.oddConj v) = hlsMom (S.hlsBeta u v • hlsMomUnit 0 0) := by
  obtain ⟨c, hc⟩ := S.br_pos_dotPos_mom hu (S.oddConj_mem_wt_pos hv)
  have hcoef : S.hlsBeta u v = c := by
    rw [hlsBeta, hc]
    simp [hlsMom, hlsMomUnit, Matrix.single_apply]
  rw [hcoef, hc]

theorem hlsBeta_add_left (u u' v : V) :
    S.hlsBeta (u + u') v = S.hlsBeta u v + S.hlsBeta u' v := by
  simp [hlsBeta]

theorem hlsBeta_smul_left (c : ℂ) (u v : V) :
    S.hlsBeta (c • u) v = c * S.hlsBeta u v := by
  simp [hlsBeta]

theorem hlsBeta_herm {u v : V} (hu : u ∈ S.wt 1 0) (hv : v ∈ S.wt 1 0) :
    (starRingEnd ℂ) (S.hlsBeta v u) = S.hlsBeta u v := by
  have h := S.oddConj_br u (S.oddConj v)
  rw [S.oddConj_conj v, S.br_pos_beta hu hv, hlsEvenConj_mom] at h
  have hH : ((S.hlsBeta u v • hlsMomUnit 0 0)ᴴ : Matrix (Fin 2) (Fin 2) ℂ)
      = (starRingEnd ℂ) (S.hlsBeta u v) • hlsMomUnit 0 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hlsMomUnit, Matrix.conjTranspose_apply]
  rw [hH] at h
  have h2 : S.br v (S.oddConj u) = hlsMom ((starRingEnd ℂ) (S.hlsBeta u v) • hlsMomUnit 0 0) := by
    rw [← h, S.br_symm]
  have h3 := S.br_pos_beta hv hu
  rw [h2] at h3
  have hval := congrArg (fun X : HLSEven B => X.2.2.1 0 0) h3
  simp only [hlsMom, hlsMomUnit, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul,
    and_self, if_true, mul_one] at hval
  rw [← hval]
  simp

/-- The state's energy along `P_{1 1̇}` is a positive real. -/
theorem state_mom_unit_pos :
    0 < (S.state (hlsMom (B := B) (hlsMomUnit 0 0))).re ∧
      (S.state (hlsMom (B := B) (hlsMomUnit 0 0))).im = 0 := by
  have h := S.state_mom_posDef.diag_pos (i := 0)
  have hval : (Matrix.of fun a b => S.state (hlsMom (B := B) (Matrix.single a b (1 : ℂ)))) 0 0
      = S.state (hlsMom (B := B) (hlsMomUnit 0 0)) := rfl
  rw [hval, Complex.lt_def] at h
  exact ⟨by simpa using h.1, by simpa using h.2.symm⟩

theorem hlsBeta_pos {u : V} (hu : u ∈ S.wt 1 0) (hu0 : u ≠ 0) : 0 < (S.hlsBeta u u).re := by
  have hstate := S.state_positive u hu0
  rw [S.br_pos_beta hu hu, hlsMom_smul, map_smul, smul_eq_mul] at hstate
  obtain ⟨hs, hs0⟩ := S.state_mom_unit_pos
  have hreal : (S.hlsBeta u u).im = 0 := by
    have h := S.hlsBeta_herm hu hu
    have := congrArg Complex.im h
    simp [Complex.conj_im] at this
    linarith
  have hmul : (S.hlsBeta u u * S.state (hlsMom (B := B) (hlsMomUnit 0 0))).re
      = (S.hlsBeta u u).re * (S.state (hlsMom (B := B) (hlsMomUnit 0 0))).re := by
    rw [Complex.mul_re, hreal, zero_mul, sub_zero]
  rw [hmul] at hstate
  by_contra hcon
  simp only [not_lt] at hcon
  nlinarith [hstate, hs, hcon]


/-- **The orthonormal supercharge basis.**  Positivity diagonalizes the coefficient form of
`{Q, Q̄}`, producing `N` supercharges obeying `{Q^I_1, Q̄^J_1̇} = 2 δ^{IJ} P_{1 1̇}` and spanning
the undotted highest-weight sector. -/
theorem exists_supercharge_basis :
    ∃ (N : ℕ) (Q : Fin N → V),
      (∀ I, Q I ∈ S.wt 1 0) ∧
      (∀ I J, S.br (Q I) (S.oddConj (Q J))
        = hlsMom ((if I = J then (2 : ℂ) else 0) • hlsMomUnit 0 0)) ∧
      Submodule.span ℂ (Set.range Q) = S.wt 1 0 := by
  classical
  obtain ⟨n, e, horth, hsp⟩ :=
    hlsExistsOrthonormal (W := ↥(S.wt 1 0)) (fun u v => (2 : ℂ)⁻¹ * S.hlsBeta (u : V) (v : V))
      (fun u v w => by
        simp only [Submodule.coe_add, S.hlsBeta_add_left]
        ring)
      (fun c u v => by
        simp only [Submodule.coe_smul, S.hlsBeta_smul_left]
        ring)
      (fun u v => by
        have hc : (starRingEnd ℂ) ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
          rw [map_inv₀]
          congr 1
          simp [Complex.ext_iff]
        rw [map_mul, hc, S.hlsBeta_herm u.2 v.2])
      (fun u hu => by
        have hu0 : (u : V) ≠ 0 := fun h => hu (Subtype.ext h)
        have hb := S.hlsBeta_pos u.2 hu0
        rw [Complex.mul_re]
        norm_num
        linarith)
  refine ⟨n, fun I => ((e I : V)), fun I => (e I).2, ?_, ?_⟩
  · intro I J
    have h := horth I J
    have hbeta : S.hlsBeta ((e I : V)) ((e J : V)) = if I = J then (2 : ℂ) else 0 := by
      by_cases hIJ : I = J
      · simp only [if_pos hIJ] at h ⊢
        linear_combination 2 * h
      · simp only [if_neg hIJ] at h ⊢
        linear_combination 2 * h
    rw [S.br_pos_beta (e I).2 (e J).2, hbeta]
  · have himg : Submodule.map (S.wt 1 0).subtype (Submodule.span ℂ (Set.range e))
        = Submodule.span ℂ (Set.range fun I => ((e I : V))) := by
      rw [Submodule.map_span]
      congr 1
      ext x
      simp
    rw [← himg, hsp, Submodule.map_top, Submodule.range_subtype]

end HLSGradedSymmetry

end GaloisForLFunctions.HTGeometry
