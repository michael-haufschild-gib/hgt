import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParabolicBlockMatrices
import GaloisForLFunctions.RHTower.Artin.ArtinMonomialSpan

/-! Iterated Harish–Chandra induction is ordinary induction from the parabolic
with all the listed diagonal blocks. -/

noncomputable section
open scoped Classical

open GaloisForLFunctions

namespace GlobalTheory.GLq

variable {g : ℕ} [Fact g.Prime]

abbrev rightLevi {a b : ℕ} : twoBlockParabolic g a b →* Gn g b :=
  (MonoidHom.snd (Gn g a) (Gn g b)).comp twoBlockLevi

theorem rightLevi_surjective {a b : ℕ} : Function.Surjective (rightLevi (g := g) (a := a) (b := b)) := by
  intro B
  let p : twoBlockParabolic g a b := ⟨upperBlockUnit 1 0 B, inPar_upperBlockMatrix 1 0 B.val⟩
  exact ⟨p, congrArg Prod.snd (twoBlockLevi_upperBlockUnit 1 0 B)⟩

/-- The parabolic preserving the flag with successive dimensions given by the list. -/
def listParabolic : (L : List (Pc g)) → Subgroup (Gn g (degL L))
  | [] => ⊤
  | p :: L =>
    ((listParabolic L).comap rightLevi).map (twoBlockParabolic g p.1 (degL L)).subtype

/-- The parabolic inside the two-block parabolic obtained by imposing the tail flag. -/
abbrev tailParabolic (p : Pc g) (L : List (Pc g)) :
    Subgroup (twoBlockParabolic g p.1 (degL L)) :=
  (listParabolic L).comap rightLevi

abbrev listParabolicConsEquiv (p : Pc g) (L : List (Pc g)) :
    tailParabolic p L ≃* listParabolic (p :: L) :=
  (tailParabolic p L).equivMapOfInjective _ (twoBlockParabolic g p.1 (degL L)).subtype_injective

abbrev tailLevi (p : Pc g) (L : List (Pc g)) : tailParabolic p L →* listParabolic L where
  toFun q := ⟨rightLevi q.val, q.property⟩
  map_one' := Subtype.ext (map_one rightLevi)
  map_mul' u v := Subtype.ext (map_mul rightLevi u.val v.val)

/-- The product of the diagonal-block characters pulled back to the list parabolic. -/
def listParabolicCharacter : (L : List (Pc g)) → listParabolic L → ℂ
  | [], _ => 1
  | p :: L, x =>
    let q := (listParabolicConsEquiv p L).symm x
    listParabolicCharacter L (tailLevi p L q) * p.2 (twoBlockLevi q.val).1

/-- Ordinary induction from the list parabolic agrees with the iterated block formula. -/
theorem hcL_eq_inducedFunction_listParabolic (L : List (Pc g)) (hL : ∀ p ∈ L, IsClass p.2) :
    hcL L (degL L) = inducedFunction (listParabolic L) (listParabolicCharacter L) := by
  induction L with
  | nil =>
    change (fun _ : Gn g 0 => (1 : ℂ)) = inducedFunction ⊤ (fun _ => 1)
    exact (inducedFunction_top (fun _ : Gn g 0 => (1 : ℂ)) (fun _ _ => rfl)).symm
  | cons p L ih =>
    let P := twoBlockParabolic g p.1 (degL L)
    let Q := tailParabolic p L
    let π : P →* Gn g p.1 × Gn g (degL L) := twoBlockLevi
    let ρ : P →* Gn g (degL L) := rightLevi
    let ψ (x : P) := p.2 (π x).1
    let f (q : Q) := listParabolicCharacter L (tailLevi p L q)
    have hTail := ih (fun q hq => hL q (List.mem_cons_of_mem p hq))
    have hψ (a b : P) : ψ (a * b * a⁻¹) = ψ b := by
      change p.2 (π (a * b * a⁻¹)).1 = p.2 (π b).1
      rw [map_mul, map_mul, map_inv]
      exact hL p List.mem_cons_self (π b).1 (π a).1
    have hinner : inducedFunction Q (fun q => f q * ψ q.val) =
        (fun x : P => ψ x * hcL L (degL L) (ρ x)) := by
      rw [inducedFunction_mul_restrict Q f ψ hψ]
      funext x
      have hx : inducedFunction Q f x =
          inducedFunction (listParabolic L) (listParabolicCharacter L) (ρ x) :=
        inducedFunction_comap ρ rightLevi_surjective (listParabolic L) (listParabolicCharacter L) x
      exact (congrArg (· * ψ x) (hx.trans (congrFun hTail (ρ x)).symm)).trans (mul_comm _ _)
    let e := listParabolicConsEquiv p L
    change hc p.1 (degL L) p.2 (hcL L (degL L)) (p.1 + degL L) =
      inducedFunction (Q.map P.subtype) (fun k => f (e.symm k) * ψ (e.symm k).val)
    exact (hc_eq_inducedFunction p.2 (hcL L (degL L))).trans
      ((congrArg (inducedFunction P) hinner.symm).trans
        (inducedFunction_inducedFunction P Q (fun q => f q * ψ q.val)))

/-- The list-parabolic character is the character of a genuine representation. -/
theorem isChar_listParabolicCharacter (L : List (Pc g)) (hL : ∀ p ∈ L, IsChar p.2) :
    IsChar (listParabolicCharacter L) := by
  induction L with
  | nil =>
    let P := listParabolic ([] : List (Pc g))
    refine ⟨FDRep.of (Representation.trivial ℂ P ℂ), fun x => ?_⟩
    change LinearMap.trace ℂ ℂ ((Representation.trivial ℂ P ℂ) x) = 1
    simp [Representation.trivial]
  | cons p L ih =>
    obtain ⟨V, hV⟩ := hL p List.mem_cons_self
    obtain ⟨W, hW⟩ := ih (fun q hq => hL q (List.mem_cons_of_mem p hq))
    let P := twoBlockParabolic g p.1 (degL L)
    let Q := tailParabolic p L
    let π : P →* Gn g p.1 × Gn g (degL L) := twoBlockLevi
    let ρ := V.ρ.comp (((MonoidHom.fst _ _).comp π).comp Q.subtype)
    let τ := W.ρ.comp (tailLevi p L)
    let σ := Representation.tprod τ ρ
    let e := listParabolicConsEquiv p L
    refine ⟨FDRep.of (σ.comp e.symm.toMonoidHom), fun x => ?_⟩
    let q := e.symm x
    change (Representation.tprod τ ρ).character q =
      listParabolicCharacter L (tailLevi p L q) * p.2 (π q.val).1
    rw [Representation.char_tensor, Pi.mul_apply]
    exact congrArg₂ (· * ·) (hW (tailLevi p L q)) (hV (π q.val).1)

end GlobalTheory.GLq
