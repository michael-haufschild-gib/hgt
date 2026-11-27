import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalProductPullback

/-! A generator of the difference of two formal powers identifies the two
powers. Scaling its exponents raises its local generators to a power. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LineBundleSections

variable {X Y : Scheme.{0}} {L : LB X}

/-- A generator of a formal product gives a generator after multiplying all exponents. -/
theorem exists_gen_scaled {I : Type} [Fintype I] {f : I → (Y ⟶ X)} {d : I → ℤ}
    {t : (LB.LinComb L f d).Gen} (ht : t.IsGen) (n : ℕ) :
    ∃ v : (LB.LinComb L f (fun i => d i * (n : ℤ))).Gen, v.IsGen := by
  refine ⟨⟨fun i => t.s i ^ n⟩, fun i j => ?_⟩
  let W := LB.wchart L f i ⊓ LB.wchart L f j
  let u (k : I) : Γ(Y, W)ˣ :=
    res (le_inf (inf_le_left.trans (LB.wchart_le L f i k))
        (inf_le_right.trans (LB.wchart_le L f j k)))
      (pullU (f k) (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k)))
  let g₀ : Γ(Y, W)ˣ := (LB.LinComb L f d).g i j
  let g₁ : Γ(Y, W)ˣ := (LB.LinComb L f (fun k => d k * (n : ℤ))).g i j
  have e : g₁ = g₀ ^ n := by
    change (∏ k, u k ^ (d k * (n : ℤ))) = (∏ k, u k ^ d k) ^ n
    calc
      _ = ∏ k, (u k ^ d k) ^ n := Finset.prod_congr rfl fun k _ =>
        (zpow_mul (u k) (d k) (n : ℤ)).trans (zpow_natCast (u k ^ d k) n)
      _ = _ := Finset.prod_pow _ _ _
  let r := res (inf_le_left : W ≤ LB.wchart L f i)
  let s := res (inf_le_right : W ≤ LB.wchart L f j)
  change r (t.s i ^ n) = g₁ * s (t.s j ^ n)
  calc
    _ = r (t.s i) ^ n := map_pow _ _ _
    _ = (g₀ * s (t.s j)) ^ n := congrArg (fun v : Γ(Y, W)ˣ => v ^ n) (ht i j)
    _ = _ := (mul_pow _ _ _).trans (congrArg₂ (· * ·) e.symm (map_pow s _ _).symm)

private def chart_div_linComb (L : LB X) {I J : Type} [Fintype I] [Fintype J]
    (f : I → (Y ⟶ X)) (g : J → (Y ⟶ X)) (a : I → ℤ) (b : J → ℤ) :
    ChartPull ((LB.LinComb L f a).div (LB.LinComb L g b))
      (LB.LinComb L (Sum.elim f g) (Sum.elim a fun j => -b j)) (𝟙 Y) where
  idx i := Sum.elim i.1 i.2
  le i _ hz := Set.mem_iInter.mpr fun k => by
    cases k with
    | inl k => exact Set.mem_iInter.mp hz.1 k
    | inr k => exact Set.mem_iInter.mp hz.2 k
  g i j := by
    rw [pullLE_id]
    apply unit_ext
    intro y hy
    let M := LB.LinComb L f a
    let N := LB.LinComb L g b
    let e (k : (M.div N).ι) := Sum.elim k.1 k.2
    have h (k : (M.div N).ι) (hk : y ∈ (M.div N).U k) : y ∈ LB.wchart L (Sum.elim f g) (e k) :=
      Set.mem_iInter.mpr fun l => by
        cases l with
        | inl l => exact Set.mem_iInter.mp hk.1 l
        | inr l => exact Set.mem_iInter.mp hk.2 l
    have h₁ := gm_div N M (𝟙 Y) y i j hy
    have h₂ := gm_linComb L f a (𝟙 Y) y i.1 j.1 hy.1.1 hy.2.1
    have h₃ := gm_linComb L g b (𝟙 Y) y i.2 j.2 hy.1.2 hy.2.2
    have h₄ := gm_linComb L (Sum.elim f g) (Sum.elim a fun j => -b j) (𝟙 Y) y
      (e i) (e j) (h i hy.1) (h j hy.2)
    refine h₁.trans ((congrArg₂ (fun x z => x * z⁻¹) h₂ h₃).trans ?_)
    refine Eq.trans ?_ ((gm_res (𝟙 Y) y _ hy _).trans h₄).symm
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, e, zpow_neg, Finset.prod_inv_distrib]
    rfl

/-- A generator of the formal difference identifies the two products in their bundle charts. -/
theorem exists_iso_of_formal_difference_gen {I J U : Type} [Fintype I] [Fintype J] [Fintype U]
    (hL : L.IsLB) (f : I → (Y ⟶ X)) (g : J → (Y ⟶ X)) (a : I → ℤ) (b : J → ℤ)
    {φ : U → (Y ⟶ X)} {d : U → ℤ}
    (he : FormEq φ d (Sum.elim f g) (Sum.elim a fun j => -b j))
    (t : (LB.LinComb L φ d).Gen) (ht : t.IsGen) :
    ∃ u : LB.Iso (LB.LinComb L g b) (LB.LinComb L f a), u.IsGen := by
  obtain ⟨v, hv, -⟩ := exists_gen_of_formEq hL he t ht
  exact (chart_div_linComb L f g a b).exists_gen hv

/-- A generator of the difference between two powers identifies them. -/
theorem exists_iso_of_power_difference_gen (hL : L.IsLB) (p q : Y ⟶ X) (a b : ℤ)
    (t : (LB.LinComb L ![p, q] ![a, -b]).Gen) (ht : t.IsGen) :
    ∃ u : LB.Iso (LB.LinComb L (fun _ : PUnit => q) (fun _ => b))
      (LB.LinComb L (fun _ : PUnit => p) (fun _ => a)), u.IsGen := by
  refine exists_iso_of_formal_difference_gen hL _ _ _ _ (fun G _ k => ?_) t ht
  simp only [Fin.prod_univ_two, Fintype.prod_sum_type, Fintype.prod_unique,
    Matrix.cons_val_zero, Matrix.cons_val_one, Sum.elim_inl, Sum.elim_inr]

end GlobalTheory.LineBundleSections
