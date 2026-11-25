import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELIsomorphismGerms

/-! Transport of generators through an isomorphism of pulled-back line bundles. -/

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

section SameScheme

variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
  {K : Type} [Fintype K]

def pw (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι) :
    (Z.presheaf.stalk z)ˣ := ∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k

private theorem mem_wchart_lemma {A B : Scheme.{0}} {Idx : Type} [Fintype Idx] (M : LB A) (ψ : Idx → (B ⟶ A))
    (j : Idx → M.ι) (b : B) : b ∈ LB.wchart M ψ j ↔ ∀ k, ψ k b ∈ M.U (j k) := by
  show b ∈ ⋂ k, (ψ k).base ⁻¹' (M.U (j k) : Set A) ↔ _
  exact Set.mem_iInter

private theorem gm_res_pullU {X Y Z : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ V) (s : Γ(X, U)ˣ) :
    gm r z V (res h (pullU f U s)) = gm (r ≫ f) z U s :=
  (gm_res r z h hz _).trans (gm_pull r f z U (h hz) s)

theorem pw_trans {w : LB.Iso L' (L.pull F)} (hw : PGen w) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z)
    {p p' : K → L.ι} {q q' : K → L'.ι} (hp : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p)
    (hp' : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p') (hq : r z ∈ LB.wchart L' φ' q) (hq' : r z ∈ LB.wchart L' φ' q') :
    pw w φ' ε r z p q = trF (fun k => φ' k ≫ F) ε r z p p' * (trF φ' ε r z q q')⁻¹ * pw w φ' ε r z p' q' := by
  rw [mem_wchart_lemma] at hp hp' hq hq'
  simp only [pw, trF]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [hw Z (r ≫ φ' k) z (p k) (p' k) (q k) (q' k) (by simpa using hp k) (by simpa using hp' k)
    (by simpa using hq k) (by simpa using hq' k)]
  simp only [Category.assoc, mul_zpow, inv_zpow]

theorem exists_pw (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (p : K → L.ι) (q : K → L'.ι) :
    ∃ u : Γ(Y, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q → gm r z _ u = pw w φ' ε r z p q := by
  have hle : ∀ k, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q ≤
      φ' k ⁻¹ᵁ ((L.pull F).U (fun _ => p k) ⊓ L'.U (q k)) := by
    intro k y hy
    have h1 := (mem_wchart_lemma _ _ _ _).mp hy.1
    have h2 := (mem_wchart_lemma _ _ _ _).mp hy.2
    show φ' k y ∈ ((L.pull F).U fun _ => p k) ⊓ L'.U (q k)
    exact ⟨(mem_wchart_lemma _ _ _ _).mpr fun _ => by simpa using h1 k, h2 k⟩
  refine ⟨∏ k, res (hle k) (pullU (φ' k) ((L.pull F).U (fun _ => p k) ⊓ L'.U (q k))
    (w.s (fun _ => p k, q k))) ^ ε k, ?_⟩
  intro Z r z hz
  simp only [pw, gw, map_prod, map_zpow]
  refine Finset.prod_congr rfl fun k _ => ?_
  exact congrArg (· ^ ε k) (gm_res_pullU (φ' k) _ _ (hle k) r z hz _)

private theorem trF_self_local {M : LB X} (hM : M.IsLB) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) {j : K → M.ι} (hj : r z ∈ LB.wchart M φ j) :
    trF φ ε r z j j = 1 := by
  apply Finset.prod_eq_one
  intro k _
  exact (congrArg (· ^ ε k) (gm_self hM (r ≫ φ k) z (Set.mem_iInter.mp hj k))).trans (one_zpow _)

/-- A generator with changed trivializations determines a generator in the original charts. -/
theorem exists_up {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) : ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι), r z ∈ LB.wchart L (fun k => φ' k ≫ F) p →
        r z ∈ LB.wchart L' φ' q → gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) =
          pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
  classical
  have hcovq : ∀ y : Y, ∃ q : K → L'.ι, y ∈ LB.wchart L' φ' q := by
    intro y
    have hk : ∀ k, ∃ i, φ' k y ∈ L'.U i := fun k => exists_chart hL' (φ' k y)
    choose q hq using hk
    exact ⟨q, (mem_wchart_lemma _ _ _ _).mpr hq⟩
  choose u hu using fun p q => exists_pw w φ' ε p q
  have hle1 : ∀ p q, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q ≤
      LB.wchart L (fun k => φ' k ≫ F) p := fun _ _ => inf_le_left
  have hle2 : ∀ p q, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q ≤
      LB.wchart L' φ' q := fun _ _ => inf_le_right
  have key : ∀ {y : Y} (T P A : (Y.presheaf.stalk y)ˣ), 1 * T⁻¹ * P * (T * A) = P * A :=
    fun T P A => by rw [_root_.one_mul, _root_.mul_assoc, _root_.mul_left_comm P, inv_mul_cancel_left]
  have hcompat : ∀ p q q' (y : Y), y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
      y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q' →
      gm (𝟙 Y) y _ (u p q * res (hle2 p q) (a.s q)) =
        gm (𝟙 Y) y _ (u p q' * res (hle2 p q') (a.s q')) := by
    intro p q q' y h1 h2
    have h1' : (𝟙 Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := by simpa using h1
    have h2' : (𝟙 Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q' := by simpa using h2
    rw [map_mul, map_mul, hu p q Y (𝟙 Y) y h1', hu p q' Y (𝟙 Y) y h2', gm_res (𝟙 Y) y (hle2 p q) h1' (a.s q),
      gm_res (𝟙 Y) y (hle2 p q') h2' (a.s q'), pw_trans hw φ' ε (𝟙 Y) y h1'.1 h1'.1 h1'.2 h2'.2,
      trF_self_local hL _ ε (𝟙 Y) y h1'.1, gen_trans ha (𝟙 Y) y h1.2 h2.2]
    exact key _ _ _
  have hglue : ∀ p, ∃ s : Γ(Y, LB.wchart L (fun k => φ' k ≫ F) p)ˣ, ∀ q,
      res (hle1 p q) s = u p q * res (hle2 p q) (a.s q) := fun p =>
    glue_unit _ (fun q => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q) (hle1 p)
      (fun y hy => Opens.mem_iSup.2 ⟨(hcovq y).choose, hy, (hcovq y).choose_spec⟩)
      (fun q => u p q * res (hle2 p q) (a.s q)) (fun q q' y hy => hcompat p q q' y hy.1 hy.2)
  choose ts hts using hglue
  have hval : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (ts p) =
        pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
    intro Z r z p q hp hq
    have hpq : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨hp, hq⟩
    rw [← gm_res r z (hle1 p q) hpq (ts p), hts p q, map_mul, hu p q Z r z hpq,
      gm_res r z (hle2 p q) hpq (a.s q)]
  refine ⟨⟨ts⟩, ?_, fun Z r z p q hp hq => hval Z r z p q hp hq⟩
  apply isGen_of_gm
  intro y p p' hp hp'
  obtain ⟨q, hq⟩ := hcovq y
  have hp1 : (𝟙 Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p := by simpa using hp
  have hp1' : (𝟙 Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p' := by simpa using hp'
  have hq1 : (𝟙 Y) y ∈ LB.wchart L' φ' q := by simpa using hq
  show gm (𝟙 Y) y _ (ts p) = _ * gm (𝟙 Y) y _ (ts p')
  rw [hval Y (𝟙 Y) y p q hp1 hq1, hval Y (𝟙 Y) y p' q hp1' hq1,
    pw_trans hw φ' ε (𝟙 Y) y hp1 hp1' hq1 hq1, trF_self_local hL' φ' ε (𝟙 Y) y hq1, inv_one, _root_.mul_one,
    _root_.mul_assoc]

end SameScheme

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

/-- Pull back a generator and express it in the new trivializations. -/
theorem exists_gen_move (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : PGen w)
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (h : Y' ⟶ Y)
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧ PMaps w φ' φ ε a t h := by
  classical
  let O : (K → L'.ι) → (K → L.ι) → Y'.Opens := fun q p =>
    LB.wchart L' φ' q ⊓ LB.wchart (L.pull F) φ' (fun k _ => p k)
  have le1 : ∀ q p k, O q p ≤ φ' k ⁻¹ᵁ ((L.pull F).U (fun _ => p k) ⊓ L'.U (q k)) := fun q p k y hy =>
    ⟨Set.mem_iInter.1 hy.2 k, Set.mem_iInter.1 hy.1 k⟩
  have le2 : ∀ q p, O q p ≤ h ⁻¹ᵁ LB.wchart L φ p := fun q p y hy => Set.mem_iInter.2 fun k => by
    have := mem_pull.1 (Set.mem_iInter.1 hy.2 k)
    show φ k (h y) ∈ L.U (p k)
    exact (congrArg (fun g => g y) (hc k)).symm ▸ this
  let v : ∀ q p, Γ(Y', O q p)ˣ := fun q p =>
    (∏ k, res (le1 q p k) (pullU (φ' k) _ (w.s (fun _ => p k, q k))) ^ ε k)⁻¹ * res (le2 q p) (pullU h _ (t.s p))
  have germ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) q p, r z ∈ O q p →
      gm r z (O q p) (v q p) = (∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k)⁻¹ * gm (r ≫ h) z (LB.wchart L φ p) (t.s p) := by
    intro Z r z q p hz
    have m2 := le2 q p hz
    show gm r z (O q p) ((∏ k, _)⁻¹ * _) = _
    rw [map_mul, map_inv, map_prod]
    refine congrArg₂ (· * ·) (congrArg (·⁻¹) (Finset.prod_congr rfl fun k _ => ?_))
      ((gm_res r z (le2 q p) hz _).trans (gm_pull r h z _ m2 _))
    have m := le1 q p k hz
    exact (map_zpow _ _ _).trans (congrArg (· ^ ε k) ((gm_res r z (le1 q p k) hz _).trans (gm_pull r (φ' k) z _ m _)))
  have memO : ∀ q (y : Y'), y ∈ LB.wchart L' φ' q → ∃ p, y ∈ O q p := fun q y hy => by
    choose p hp using fun k => exists_chart hL (F (φ' k y))
    exact ⟨p, hy, Set.mem_iInter.2 fun k => mem_pull.2 (hp k)⟩
  have glue : ∀ q, ∃ s : Γ(Y', LB.wchart L' φ' q)ˣ, ∀ p, res (inf_le_left : O q p ≤ _) s = v q p := by
    intro q
    refine glue_unit _ (O q) (fun p => inf_le_left) (fun y hy => ?_) (v q) fun p p' y hy => ?_
    · obtain ⟨p, hp⟩ := memO q y hy
      exact Opens.mem_iSup.2 ⟨p, hp⟩
    · rw [germ _ _ y q p hy.1, germ _ _ y q p' hy.2]
      have hp : ∀ k, F (φ' k y) ∈ L.U (p k) := fun k => mem_pull.1 (Set.mem_iInter.1 hy.1.2 k)
      have hp' : ∀ k, F (φ' k y) ∈ L.U (p' k) := fun k => mem_pull.1 (Set.mem_iInter.1 hy.2.2 k)
      have hq : ∀ k, φ' k y ∈ L'.U (q k) := fun k => Set.mem_iInter.1 hy.1.1 k
      have e1 : ∀ k, gw w (𝟙 Y' ≫ φ' k) y (p k) (q k) =
          gm (φ' k ≫ F) y _ (L.g (p k) (p' k)) * gw w (𝟙 Y' ≫ φ' k) y (p' k) (q k) := fun k => by
        rw [Category.id_comp, hw _ (φ' k) y (p k) (p' k) (q k) (q k) (hp k) (hp' k) (hq k) (hq k),
          gm_self hL' _ y (hq k), inv_one, mul_one]
      have e2 : trF φ ε (𝟙 Y' ≫ h) y p p' = ∏ k, gm (φ' k ≫ F) y _ (L.g (p k) (p' k)) ^ ε k :=
        Finset.prod_congr rfl fun k _ => by rw [Category.id_comp, ← hc k]
      rw [gen_trans ht (𝟙 Y' ≫ h) y (le2 q p hy.1) (le2 q p' hy.2), e2]
      simp only [e1, mul_zpow, Finset.prod_mul_distrib, mul_inv_rev]
      rw [mul_assoc, inv_mul_cancel_left]
  choose s hs using glue
  have vals : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) q p, r z ∈ O q p →
      gm r z (LB.wchart L' φ' q) (s q) =
        (∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k)⁻¹ * gm (r ≫ h) z (LB.wchart L φ p) (t.s p) := by
    intro Z r z q p hz
    rw [← gm_res r z (inf_le_left : O q p ≤ _) hz, hs q p, germ Z r z q p hz]
  refine ⟨⟨s⟩, fun q q' => unit_ext fun y hy => ?_, fun Z r z p q hp hq => ?_⟩
  · have hq : ∀ k, φ' k y ∈ L'.U (q k) := fun k => Set.mem_iInter.1 hy.1 k
    have hq' : ∀ k, φ' k y ∈ L'.U (q' k) := fun k => Set.mem_iInter.1 hy.2 k
    choose p hp using fun k => exists_chart hL (F (φ' k y))
    have m : y ∈ O q p := ⟨hy.1, Set.mem_iInter.2 fun k => mem_pull.2 (hp k)⟩
    have m' : y ∈ O q' p := ⟨hy.2, Set.mem_iInter.2 fun k => mem_pull.2 (hp k)⟩
    rw [gm_res _ y _ hy, map_mul, gm_res _ y _ hy]
    show gm (𝟙 Y') y (LB.wchart L' φ' q) (s q) = gm (𝟙 Y') y (LB.wchart L' φ' q ⊓ LB.wchart L' φ' q')
      ((LB.LinComb L' φ' ε).g q q') * gm (𝟙 Y') y (LB.wchart L' φ' q') (s q')
    rw [gm_linComb L' φ' ε (𝟙 Y') y q q' hy.1 hy.2, vals _ _ y q p m, vals _ _ y q' p m']
    have e3 : ∀ k, gw w (𝟙 Y' ≫ φ' k) y (p k) (q k) =
        (gm (𝟙 Y' ≫ φ' k) y _ (L'.g (q k) (q' k)))⁻¹ * gw w (𝟙 Y' ≫ φ' k) y (p k) (q' k) := fun k => by
      rw [Category.id_comp, hw _ (φ' k) y (p k) (p k) (q k) (q' k) (hp k) (hp k) (hq k) (hq' k),
        gm_self hL _ y (hp k), one_mul]
    simp only [e3, mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, mul_inv_rev, inv_inv]
    exact (congrArg (· * _) (mul_comm _ _)).trans (mul_assoc _ _ _)
  · have m : r z ∈ O q p := ⟨Set.mem_iInter.2 hq, Set.mem_iInter.2 fun k => mem_pull.2 (hp k)⟩
    show _ = _ * gm r z (LB.wchart L' φ' q) (s q)
    rw [vals Z r z q p m, mul_inv_cancel_left]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
