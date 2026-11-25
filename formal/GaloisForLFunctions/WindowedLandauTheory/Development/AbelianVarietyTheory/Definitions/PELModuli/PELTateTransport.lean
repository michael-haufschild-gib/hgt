import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.IntegralPELModuli

/-! A group isomorphism transports the compatible prime-to-p Tate structure. -/

noncomputable section

namespace GlobalTheory.UPel.HT.TateIsoO

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {k Q Q' : Type} [Field k] [Group Q] [Group Q']
  {act : D.O → Q → Q} {act' : D.O → Q' → Q'}
  {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}

/-- Transport along an equivariant isomorphism that carries back the pairing. -/
def transport (I : TateIsoO D k Q act e) (u : Q' ≃* Q)
    (hact : ∀ b q, u (act' b q) = act b (u q))
    (hpair : ∀ n x y z, e n (u x) (u y) z → e' n x y z) :
    TateIsoO D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n x := u.symm (I.ev n x)
  add n x y := by rw [I.add, map_mul]
  lin n b x := u.injective (by rw [u.apply_symm_apply, hact, u.apply_symm_apply, I.lin])
  ker n hn hp x := (map_eq_one_iff u.symm u.symm.injective).trans (I.ker n hn hp x)
  onto n hn hp q := by
    rw [← map_eq_one_iff u u.injective, map_pow, I.onto n hn hp (u q)]
    exact exists_congr fun x => u.symm_apply_eq.symm
  tower n m hn hm hnm x := by rw [← map_pow, I.tower n m hn hm hnm x]
  isom n hn hp x y := by
    refine hpair _ _ _ _ ?_
    rw [u.apply_symm_apply, u.apply_symm_apply]
    exact I.isom n hn hp x y

end GlobalTheory.UPel.HT.TateIsoO
