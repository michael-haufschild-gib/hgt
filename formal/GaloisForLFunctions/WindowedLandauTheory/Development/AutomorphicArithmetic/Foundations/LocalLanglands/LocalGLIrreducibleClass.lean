import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothIrreducibleTwist
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.CuspidalDeterminantTwist

/-! Irreducible general linear classes are graded by rank.
Cuspidality is invariant under equivalence and determinant twisting. -/

noncomputable section

open Matrix Representation GlobalTheory.PRep

namespace GlobalTheory.GLp

variable {k : Type} [Field k] [TopologicalSpace k] {n : ℕ}

theorem isSmoothCuspidal_of_equiv {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) k) V} {σ : Representation ℂ (GL (Fin n) k) W}
    (e : ρ.Equiv σ) (hρ : IsSmoothCuspidal ρ) : IsSmoothCuspidal σ := by
  have hE (g : GL (Fin n) k) (x : V) : e.toLinearEquiv (ρ g x) = σ g (e.toLinearEquiv x) :=
    IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g x
  refine ⟨fun w => ?_, fun b hb => ?_⟩
  · obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective w
    have he : {g | σ g (e.toLinearEquiv x) = e.toLinearEquiv x} = {g | ρ g x = x} :=
      Set.ext fun g => by simp only [Set.mem_setOf_eq, ← hE, e.toLinearEquiv.injective.eq_iff]
    exact he.symm ▸ hρ.1 x
  · let H := blockUnipotentRadical k b
    let r : Representation ℂ H V := ρ.comp H.subtype
    let s : Representation ℂ H W := σ.comp H.subtype
    have hmap (x : V) (hx : x ∈ Coinvariants.ker r) :
        e.toLinearEquiv x ∈ Coinvariants.ker s := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨⟨g, v⟩, rfl⟩ := hx
        change e.toLinearEquiv (ρ g.val v - v) ∈ Coinvariants.ker s
        rw [map_sub, hE]
        exact Coinvariants.sub_mem_ker g (e.toLinearEquiv v)
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
    refine eq_top_iff.mpr fun w _ => ?_
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective w
    exact hmap x ((hρ.2 b hb).symm ▸ Submodule.mem_top)

/-- Smooth irreducible general linear representations up to equivalence, with rank. -/
abbrev IrrGL (k : Type) [Field k] [TopologicalSpace k] := Σ n : ℕ, IrrCl (GL (Fin n) k)

namespace IrrGL

def IsCusp (x : IrrGL k) : Prop :=
  0 < x.1 ∧ IsSmoothCuspidal x.2.rep.ρ

theorem isCusp_mk_iff (σ : IrrRep (GL (Fin n) k)) :
    IsCusp (⟨n, σ.cl⟩ : IrrGL k) ↔ 0 < n ∧ IsSmoothCuspidal σ.ρ := by
  let c := σ.cl
  obtain ⟨e⟩ := IrrRep.cl_eq_iff.mp c.cl_rep
  exact and_congr_right fun _ => ⟨isSmoothCuspidal_of_equiv e, isSmoothCuspidal_of_equiv e.symm⟩

variable [IsTopologicalRing k]

def detTwist (x : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsOpen (χ.ker : Set kˣ)) : IrrGL k :=
  ⟨x.1, x.2.twist (χ.comp GeneralLinearGroup.det) (hχ.preimage GeneralLinearGroup.continuous_det)⟩

theorem detTwist_mul (x : IrrGL k) (χ ψ : kˣ →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set kˣ)) (hψ : IsOpen (ψ.ker : Set kˣ))
    (hχψ : IsOpen ((χ * ψ).ker : Set kˣ)) :
    (x.detTwist χ hχ).detTwist ψ hψ = x.detTwist (χ * ψ) hχψ := by
  let d := GeneralLinearGroup.det (n := Fin x.1) (R := k)
  let a := χ.comp d
  let b := ψ.comp d
  have ha : IsOpen (a.ker : Set (GL (Fin x.1) k)) :=
    hχ.preimage GeneralLinearGroup.continuous_det
  have hb : IsOpen (b.ker : Set (GL (Fin x.1) k)) :=
    hψ.preimage GeneralLinearGroup.continuous_det
  have he : a * b = (χ * ψ).comp d := MonoidHom.ext fun _ => rfl
  let T := {c : GL (Fin x.1) k →* ℂˣ // IsOpen (c.ker : Set (GL (Fin x.1) k))}
  let c : T := ⟨a * b, isOpen_ker_mul a b ha hb⟩
  let c' : T := ⟨(χ * ψ).comp d, hχψ.preimage GeneralLinearGroup.continuous_det⟩
  have hcc : c = c' := Subtype.ext he
  exact congrArg (Sigma.mk x.1) ((IrrCl.twist_mul x.2 a b ha hb c.prop).trans
    (congrArg (fun z : T => x.2.twist z.val z.prop) hcc))

theorem detTwist_congr (x : IrrGL k) {χ ψ : kˣ →* ℂˣ}
    (hχ : IsOpen (χ.ker : Set kˣ)) (hψ : IsOpen (ψ.ker : Set kˣ))
    (e : χ = ψ) : x.detTwist χ hχ = x.detTwist ψ hψ := by
  subst ψ
  rfl

@[simp] theorem detTwist_one (x : IrrGL k) (hχ : IsOpen ((1 : kˣ →* ℂˣ).ker : Set kˣ)) :
    x.detTwist 1 hχ = x := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  change x.2.twist ((1 : kˣ →* ℂˣ).comp (GeneralLinearGroup.det (n := Fin x.1))) _ = x.2
  have he : (1 : kˣ →* ℂˣ).comp (GeneralLinearGroup.det (n := Fin x.1)) = 1 := MonoidHom.ext fun _ => rfl
  simpa only [he, IrrCl.twist_one]

theorem detTwist_inv (x : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsOpen (χ.ker : Set kˣ)) :
    (x.detTwist χ hχ).detTwist χ⁻¹ (isOpen_ker_inv χ hχ) = x := by
  have h := isOpen_ker_mul χ χ⁻¹ hχ (isOpen_ker_inv χ hχ)
  have h₁ : IsOpen ((1 : kˣ →* ℂˣ).ker : Set kˣ) := by simp
  rw [detTwist_mul _ _ _ _ _ h]
  exact (x.detTwist_congr h h₁ (MonoidHom.ext fun z => mul_inv_cancel (χ z))).trans
    (detTwist_one x h₁)

theorem IsCusp.detTwist {x : IrrGL k} (hx : x.IsCusp) (χ : kˣ →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set kˣ)) : (x.detTwist χ hχ).IsCusp := by
  let σ := x.2.rep
  let τ := σ.twist (χ.comp GeneralLinearGroup.det) (hχ.preimage GeneralLinearGroup.continuous_det)
  have he : (⟨x.1, τ.cl⟩ : IrrGL k) = x.detTwist χ hχ := by
    apply congrArg (Sigma.mk x.1)
    simp only [τ, IrrRep.cl_twist, σ, IrrCl.cl_rep]
  rw [← he, isCusp_mk_iff]
  exact ⟨hx.1, isSmoothCuspidal_of_determinantTwist σ.ρ hx.2 χ hχ⟩

theorem isCusp_detTwist_iff (x : IrrGL k) (χ : kˣ →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set kˣ)) : (x.detTwist χ hχ).IsCusp ↔ x.IsCusp := by
  refine ⟨fun hx => ?_, fun hx => hx.detTwist χ hχ⟩
  let hχ' := isOpen_ker_inv χ hχ
  have h := hx.detTwist χ⁻¹ hχ'
  have he : χ * χ⁻¹ = 1 := MonoidHom.ext fun z => mul_inv_cancel (χ z)
  simpa only [detTwist_mul _ _ _ _ _ (isOpen_ker_mul _ _ hχ hχ'), he, detTwist_one] using h

end IrrGL

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.IrrGL.isCusp_detTwist_iff
