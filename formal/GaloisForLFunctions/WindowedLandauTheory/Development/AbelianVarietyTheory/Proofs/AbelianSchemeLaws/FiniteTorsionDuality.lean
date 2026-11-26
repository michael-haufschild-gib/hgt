import Mathlib.GroupTheory.FiniteAbelian.Duality

/-! A nondegenerate skew pairing identifies a finite torsion group with its character group. -/

namespace GlobalTheory.CommPairing

/-- Every character of the n-torsion group is pairing with a unique torsion element. -/
theorem existsUnique_pairing_eq_character {H M : Type} [CommGroup H] [CommMonoid M] (n : ℕ)
    [NeZero n] [HasEnoughRootsOfUnity M n] [Finite {x : H // x ^ n = 1}]
    (W : H → H → Mˣ → Prop)
    (hex : ∀ x y : H, x ^ n = 1 → y ^ n = 1 → ∃! c, W x y c)
    (hmul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c'))
    (hskew : ∀ x y c, W x y c → W y x c⁻¹)
    (hnd : ∀ x : H, x ^ n = 1 → (∀ y : H, y ^ n = 1 → W x y 1) → x = 1)
    (χ : {x : H // x ^ n = 1} → Mˣ)
    (hχ : ∀ x y, χ ⟨x.1 * y.1, by rw [mul_pow, x.2, y.2, one_mul]⟩ = χ x * χ y) :
    ∃! b : H, b ^ n = 1 ∧ ∀ x : {x : H // x ^ n = 1}, W x.1 b (χ x) := by
  classical
  let G : Subgroup H := (powMonoidHom n : H →* H).ker
  have hg (x : G) : (x : H) ^ n = 1 := x.2
  letI : Finite G := inferInstanceAs (Finite {x : H // x ^ n = 1})
  choose e he huniq using fun x y : G => hex x y (hg x) (hg y)
  have hl (x x' y : G) : e (x * x') y = e x y * e x' y :=
    (huniq _ _ _ (hmul _ _ _ _ _ (he x y) (he x' y))).symm
  have hs (x y : G) : e y x = (e x y)⁻¹ := (huniq _ _ _ (hskew _ _ _ (he x y))).symm
  have hr (x y y' : G) : e x (y * y') = e x y * e x y' := by
    rw [hs (y * y') x, hl, hs y x, hs y' x, mul_inv]
  let Φ : G →* (G →* Mˣ) := MonoidHom.mk' (fun b => MonoidHom.mk' (fun x => e x b) (fun x x' => hl x x' b))
    (fun b b' => MonoidHom.ext fun x => hr x b b')
  have hΦ (b x : G) : Φ b x = e x b := rfl
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    refine Subtype.ext (hnd b (hg b) fun y hy => ?_)
    have h₁ : e ⟨y, hy⟩ b = 1 := by rw [← hΦ, hb]; rfl
    have h₂ := he b ⟨y, hy⟩
    rwa [hs, h₁, inv_one] at h₂
  letI : HasEnoughRootsOfUnity M (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd M (n := n)
      (Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (hg g))
  have hcard := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G M
  letI : Finite (G →* Mˣ) := Nat.finite_of_card_ne_zero (hcard ▸ Nat.card_pos.ne')
  have hbij : Function.Bijective Φ := hinj.bijective_of_nat_card_le hcard.le
  let χ' : G →* Mˣ := MonoidHom.mk' (fun x => χ ⟨x.1, hg x⟩)
    (fun x y => hχ ⟨x.1, hg x⟩ ⟨y.1, hg y⟩)
  obtain ⟨b, hb⟩ := hbij.2 χ'
  refine ⟨b, ⟨hg b, fun x => ?_⟩, ?_⟩
  · have h₁ : e ⟨x.1, x.2⟩ b = χ x := by rw [← hΦ, hb]; rfl
    rw [← h₁]
    exact he ⟨x.1, x.2⟩ b
  · rintro b' ⟨hb', h⟩
    have e : (⟨b', hb'⟩ : G) = b := by
      apply hinj
      rw [hb]
      ext1 x
      rw [hΦ]
      exact (huniq x ⟨b', hb'⟩ _ (h ⟨x.1, hg x⟩)).symm
    exact congrArg Subtype.val e

end GlobalTheory.CommPairing
