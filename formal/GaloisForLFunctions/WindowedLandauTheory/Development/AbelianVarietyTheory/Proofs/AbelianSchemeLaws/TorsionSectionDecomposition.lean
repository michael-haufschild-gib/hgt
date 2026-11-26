import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.WeilTranslationWeights
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalWeightDescent
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.TorsionSectionWeights

/-! Sections of the quadratic power decompose into torsion character spaces,
each isomorphic to the section module of the original power. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TwistTranslate GlobalTheory.FlatDescent GlobalTheory.CommPairing
open scoped CategoryTheory.Obj

namespace GlobalTheory.MulSplit

attribute [local instance] Over.cartesianMonoidalCategory

open GrpTangent (mulN comp_mulN finiteEtaleSurjective_mulN isMonHom_mulN)

variable {K : Type} [Field K] [IsAlgClosed K] {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}

private theorem weight_module (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L)
    (hK : KTriv A L) (hrig : ∃ t : (L.pull η[A].left).Gen, t.IsGen)
    (hsym : ∀ s : Spec (.of K), ∃ U : (Spec (.of K)).Opens, s ∈ U ∧
      ∃ t : (LB.LinComb L (K := Fin 2)
        ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]).Gen, t.IsGen)
    (n j : ℕ) (hn : (n : K) ≠ 0) (hj : j ≠ 0)
    (χ : letI := hA.comm
      (powMonoidHom n : (𝟙_ (Over (Spec (.of K))) ⟶ A) →* _).ker →* Γ(Spec (.of K), ⊤)ˣ) :
    letI := hA.comm
    let G := (powMonoidHom n : (𝟙_ (Over (Spec (.of K))) ⟶ A) →* _).ker
    let q := (mulN A n).left
    ∃ f : Sg L A.hom (Finsupp.single (𝟙 A.left) (j : ℤ)) →ₗ[Γ(Spec (.of K), ⊤)] Vals L A.hom,
      Function.Injective f ∧ ∀ v, (∃ x, f x = v) ↔
        v ∈ Sg L A.hom (Finsupp.single q (j : ℤ)) ∧
          ∀ y : G, pl L (translate A y.1).left (Over.w _) v = (χ y).val • v := by
  letI := hA.comm
  letI := hA.smooth
  letI := hA.proper
  letI := hA.geomConnected
  letI : IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  let q := mulN A n
  let T := 𝟙_ (Over (Spec (.of K)))
  let G := (powMonoidHom n : (T ⟶ A) →* (T ⟶ A)).ker
  let e : K ≃+* Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  have hunit : IsUnit (n : Γ(Spec (.of K), ⊤)) := by
    simpa only [map_natCast] using (Ne.isUnit hn).map e.toRingHom
  obtain ⟨hfin, het, hsur⟩ := finiteEtaleSurjective_mulN A hunit
  letI : IsFinite q.left := hfin
  letI : Etale q.left := het
  letI : Surjective q.left := hsur
  letI : IsMonHom q := isMonHom_mulN A n
  let τ (y : G) : A ⟶ A := translate A y.1
  have hτq (y : G) : τ y ≫ q = q := by
    change translate A y.1 ≫ mulN A n = mulN A n
    rw [translate_comp_mulN, show y.1 ^ n = 1 from y.2, translate_one, Category.comp_id]
  have hD : Descends q.left (fun y : G => (τ y).left) := by
    have H := descends_of_etale_isogeny q
    refine ⟨H.1, fun U v hv => H.2 U v fun y => ?_⟩
    exact hv ⟨y.1, (comp_mulN y.1 n).symm.trans y.2⟩
  obtain ⟨b, u, hu, huv⟩ := exists_section_weight_generator hA hL hAmp hK n hn χ
  obtain ⟨d, -, t, ht⟩ := exists_gen_twisted_pow_translate hA hL hAmp hrig hsym j hj b
  obtain ⟨w, hw, -⟩ := exists_isG (p := A.hom) hL t ht
  let D : (A.left ⟶ A.left) →₀ ℤ :=
    Finsupp.single (𝟙 A.left) ((j : ℤ) - 1) + Finsupp.single (translate A b).left 1
  have hDq : D.mapDomain (q.left ≫ ·) +
        (Finsupp.single q.left 1 + Finsupp.single (q.left ≫ (translate A b).left) (-1)) =
      Finsupp.single q.left (j : ℤ) := by
    dsimp only [D]
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single,
      Finsupp.mapDomain_single, Category.comp_id, Finsupp.single_sub, Finsupp.single_neg]
    abel
  obtain ⟨f, hf, hr⟩ := hD.weight hL (Over.w q)
    (fun y => Over.w (τ y)) (fun y => congrArg Over.Hom.left (hτq y))
    (D := D) (F := Finsupp.single q.left (j : ℤ)) hu (fun y => χ y) huv hDq
  have hd (x y : T ⟶ A) (h : y * x = 1) :
      (translate A x).left ≫ (translate A y).left = 𝟙 A.left :=
    congrArg Over.Hom.left ((translate_comp x y).trans ((congrArg (translate A) h).trans translate_one))
  obtain ⟨a⟩ := pl_equiv hL (Over.w (translate A d)) (Over.w (translate A d⁻¹))
    (hd d d⁻¹ (inv_mul_cancel _)) (hd d⁻¹ d (mul_inv_cancel _))
    (D := Finsupp.single (𝟙 A.left) (j : ℤ))
    (E := Finsupp.single (translate A d).left (j : ℤ)) (by
      rw [Finsupp.mapDomain_single, Category.comp_id])
  have hsum : dv (![𝟙 A.left, (translate A b).left, (translate A d).left] : Fin 3 → (A.left ⟶ A.left))
        ![(j : ℤ) - 1, 1, -(j : ℤ)] = D + Finsupp.single (translate A d).left (-(j : ℤ)) :=
    Fin.sum_univ_three _
  obtain ⟨b'⟩ := hw.equiv hL (E := Finsupp.single (translate A d).left (j : ℤ)) (F := D) (by
    rw [hsum, Finsupp.single_neg]
    abel)
  let c := a.trans b'
  refine ⟨f.comp c.toLinearMap, hf.comp c.injective, fun v => (Iff.trans ?_ (hr v))⟩
  exact ⟨fun ⟨x, hx⟩ => ⟨c x, hx⟩, fun ⟨x, hx⟩ => ⟨c.symm x,
    (congrArg f (c.apply_symm_apply x)).trans hx⟩⟩

/-- Sections of the power of degree `n^2 * j` are a product of copies of
the degree `j` section module indexed by the rational `n`-torsion group. -/
theorem sections_mulPull_split (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L)
    (hK : KTriv A L) (hrig : ∃ t : (L.pull η[A].left).Gen, t.IsGen)
    (hsym : ∀ s : Spec (.of K), ∃ U : (Spec (.of K)).Opens, s ∈ U ∧
      ∃ t : (LB.LinComb L (K := Fin 2)
        ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]).Gen, t.IsGen)
    (n j : ℕ) (hn : (n : K) ≠ 0) (hj : j ≠ 0) :
    Nonempty (Sg L A.hom (Finsupp.single (𝟙 A.left) ((n : ℤ) ^ 2 * (j : ℤ))) ≃ₗ[Γ(Spec (.of K), ⊤)]
      ({y : 𝟙_ (Over (Spec (.of K))) ⟶ A // y ^ n = 1} →
        Sg L A.hom (Finsupp.single (𝟙 A.left) (j : ℤ)))) := by
  letI := hA.comm
  let T := 𝟙_ (Over (Spec (.of K)))
  let R := Γ(Spec (.of K), ⊤)
  let q := mulN A n
  let G := (powMonoidHom n : (T ⟶ A) →* (T ⟶ A)).ker
  letI : Finite G := finite_prime_to_char_torsion hA n hn
  letI : NeZero (n : K) := ⟨hn⟩
  letI : NeZero n := .of_neZero_natCast K
  letI : HasEnoughRootsOfUnity R n := spec_hasEnoughRootsOfUnity K n hn
  let eK : K ≃+* R := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  letI : IsDomain R := eK.symm.toMulEquiv.isDomain K
  have hunit : IsUnit (n : R) := by simpa only [map_natCast] using (Ne.isUnit hn).map eK.toRingHom
  let τ (y : G) : A ⟶ A := translate A y.1
  have hτq (y : G) : τ y ≫ q = q := by
    change translate A y.1 ≫ mulN A n = mulN A n
    rw [translate_comp_mulN, show y.1 ^ n = 1 from y.2, translate_one, Category.comp_id]
  have hτ1 : τ 1 = 𝟙 A := translate_one
  have hτmul (x y : G) : τ x ≫ τ y = τ (x * y) :=
    (translate_comp x.1 y.1).trans (congrArg (translate A) (mul_comm y.1 x.1))
  let ρ : Representation R G (Vals L A.hom) :=
    { toFun := fun y => (pl L (τ y).left (Over.w (τ y))).toLinearMap
      map_one' := LinearMap.ext fun v => pl_id (Over.w (τ 1)) (congrArg Over.Hom.left hτ1) v
      map_mul' := fun x y => LinearMap.ext fun v =>
        (pl_pl (Over.w (τ x)) (Over.w (τ y)) (Over.w (τ (x * y)))
          (congrArg Over.Hom.left (hτmul x y)) v).symm }
  obtain ⟨e⟩ := nonempty_equiv_pi_of_weights
    (N := Sg L A.hom (Finsupp.single (𝟙 A.left) (j : ℤ))) n hunit
    (fun y : G => Subtype.ext y.2) ρ (Sg L A.hom (Finsupp.single q.left (j : ℤ)))
    (fun y v hv => pl_mem_Sg hL (Over.w (τ y)) hv (by
      rw [Finsupp.mapDomain_single, ← Over.comp_left, hτq y]))
    (weight_module hA hL hAmp hK hrig hsym n j hn hj)
  obtain ⟨s, hs⟩ := AbLaw.Cube.gen_mul_pullback_of_relAmple hA hL hAmp hrig hsym n
  obtain ⟨u, hu, -⟩ := exists_isG (p := A.hom) hL s hs
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, j = m + 1 := ⟨j - 1, by omega⟩
  obtain ⟨a⟩ := (hu.pow hL m).equiv hL
    (E := Finsupp.single q.left ((m + 1 : ℕ) : ℤ))
    (F := Finsupp.single (𝟙 A.left) ((n : ℤ) ^ 2 * ((m + 1 : ℕ) : ℤ))) (by
      have hd : dv (![𝟙 A.left, q.left] : Fin 2 → (A.left ⟶ A.left)) ![(n : ℤ) ^ 2, -1] =
          Finsupp.single (𝟙 A.left) ((n : ℤ) ^ 2) + Finsupp.single q.left (-1) := Fin.sum_univ_two _
      change _ + (m + 1) • dv (![𝟙 A.left, q.left] : Fin 2 → (A.left ⟶ A.left)) ![(n : ℤ) ^ 2, -1] = _
      rw [hd, smul_add, Finsupp.smul_single, Finsupp.smul_single]
      have hh : (m + 1) • (-1 : ℤ) = -((m + 1 : ℕ) : ℤ) := by simp
      have hh' : (m + 1) • (n : ℤ) ^ 2 = (n : ℤ) ^ 2 * ((m + 1 : ℕ) : ℤ) := by
        rw [nsmul_eq_mul, mul_comm]
      rw [hh', hh, Finsupp.single_neg]
      change _ + (Finsupp.single (𝟙 A.left) _ + (-Finsupp.single q.left _)) = _
      abel)
  exact ⟨a.symm.trans e⟩

end GlobalTheory.MulSplit
