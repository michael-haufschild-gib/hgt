import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeValueNormalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeNormalizedGluing
import Mathlib.Tactic.Abel

/-! The normalized values of a cube generator satisfy the cubical symmetry and cocycle laws. -/

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.AbLaw.Cube

/-- The normalized face, symmetry and cocycle conditions for cubical values. -/
structure IsCubicalCocycle {G U : Type} [CommGroup G] [CommGroup U]
    (θ : G → G → G → U) : Prop where
  face : ∀ x y, θ 1 x y = 1
  swapFirst : ∀ x y z, θ x y z = θ y x z
  swapLast : ∀ x y z, θ x y z = θ x z y
  cocycle : ∀ a b c d, θ (a * b) c d * θ a b d = θ a (b * c) d * θ b c d

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
variable {B T : Over S}

/-- The cube factors pulled back along a triple of points. -/
noncomputable abbrev cubeFactors (a b c : B ⟶ A) (i : Finset (Fin 3)) : B.left ⟶ A.left :=
  (lift a (lift b c)).left ≫ cubeMorphism A i

/-- Pull the cube generator back along a triple of points. -/
noncomputable abbrev cubePull (s : (cubeBundle A L).Gen) (a b c : B ⟶ A) :
    (LB.LinComb L (cubeFactors a b c) cubeExponent).Gen :=
  LB.pullGen L (cubeMorphism A) cubeExponent s (lift a (lift b c)).left

theorem cubePull_isGen {s : (cubeBundle A L).Gen} (hs : s.IsGen) (a b c : B ⟶ A) :
    (cubePull s a b c).IsGen :=
  hs.pullGen (cubeMorphism A) cubeExponent (lift a (lift b c)).left

theorem cubePull_value (s : (cubeBundle A L).Gen) (a b c : B ⟶ A) (r : T ⟶ B)
    (z : T.left) (J : (T.left ⟶ A.left) → L.ι) (hJ : Good L z J) :
    val (cubePull s a b c) r.left z J = cubeValue s (r ≫ a) (r ≫ b) (r ≫ c) z J := by
  have e : r ≫ lift a (lift b c) = lift (r ≫ a) (lift (r ≫ b) (r ≫ c)) := by simp only [comp_lift]
  exact (val_pull hJ s _ _).trans (congrArg (fun m => val s m z J) (congrArg Over.Hom.left e))

private theorem cubePull_at_identity {s : (cubeBundle A L).Gen} (hn : NormalizedCube s)
    (a b c : B ⟶ A) (r : T ⟶ B) (ha : r ≫ a = 1) (hb : r ≫ b = 1) (hc : r ≫ c = 1)
    (z : T.left) (J : (T.left ⟶ A.left) → L.ι) (hJ : Good L z J) :
    val (cubePull s a b c) r.left z J = 1 := by
  rw [cubePull_value s a b c r z J hJ, ha, hb, hc]
  exact hn T z J hJ

private theorem cubeValue_eq_of_formEq {s : (cubeBundle A L).Gen} (hL : L.IsLB) (hs : s.IsGen)
    (hn : NormalizedCube s) [IsIso B.hom.appTop] (e : 𝟙_ (Over S) ⟶ B)
    (a b c a' b' c' : B ⟶ A)
    (ha : e ≫ a = 1) (hb : e ≫ b = 1) (hc : e ≫ c = 1)
    (ha' : e ≫ a' = 1) (hb' : e ≫ b' = 1) (hc' : e ≫ c' = 1)
    (h : FormEq (cubeFactors a b c) cubeExponent (cubeFactors a' b' c') cubeExponent)
    (r : T ⟶ B) (z : T.left) (J : (T.left ⟶ A.left) → L.ι) (hJ : Good L z J) :
    cubeValue s (r ≫ a) (r ≫ b) (r ≫ c) z J = cubeValue s (r ≫ a') (r ≫ b') (r ≫ c') z J := by
  rw [← cubePull_value s a b c r z J hJ, ← cubePull_value s a' b' c' r z J hJ]
  exact normalized_values_eq hL h B.hom e.left (Over.w e)
    (cubePull_isGen hs a b c) (cubePull_isGen hs a' b' c')
    (fun p K hK => (cubePull_at_identity hn a b c e ha hb hc p K hK).trans
      (cubePull_at_identity hn a' b' c' e ha' hb' hc' p K hK).symm)
    r.left z J hJ

private theorem cubeValue_face {s : (cubeBundle A L).Gen} (hA : IsAbelianScheme A) (hL : L.IsLB)
    (hs : s.IsGen) (hn : NormalizedCube s) (x y : T ⟶ A)
    (z : T.left) (J : (T.left ⟶ A.left) → L.ι) (hJ : Good L z J) :
    cubeValue s (1 : T ⟶ A) x y z J = 1 := by
  let B := A ⊗ A
  let e : 𝟙_ (Over S) ⟶ B := lift 1 1
  let r : T ⟶ B := lift x y
  let b : B ⟶ A := fst A A
  let c : B ⟶ A := snd A A
  letI : IsIso B.hom.appTop := (hA.tensor hA).isIso_appTop
  obtain ⟨u, hu, hv⟩ := exists_gen_of_cancellation L hL (cubeFactors (1 : B ⟶ A) b c) cubeExponent
    (fun U _ k => (prod_cube (1 : B ⟶ A) b c k).trans (by
      apply Additive.ofMul.injective
      simp only [_root_.one_mul, ofMul_mul, ofMul_inv, ofMul_one]
      abel))
  have hb : e ≫ b = 1 := lift_fst _ _
  have hc : e ≫ c = 1 := lift_snd _ _
  have he := normalized_values_eq hL (fun _ _ _ => rfl) B.hom e.left (Over.w e)
    (cubePull_isGen hs (1 : B ⟶ A) b c) hu
    (fun p K hK => (cubePull_at_identity hn (1 : B ⟶ A) b c e (MonObj.comp_one e) hb hc p K hK).trans
      (hv _ e.left p K hK).symm) r.left z J hJ
  have h := cubePull_value s (1 : B ⟶ A) b c r z J hJ
  rw [MonObj.comp_one, show r ≫ b = x from lift_fst _ _, show r ≫ c = y from lift_snd _ _] at h
  exact h.symm.trans (he.trans (hv T.left r.left z J hJ))

private theorem cubeValue_cocycle {s : (cubeBundle A L).Gen} (hA : IsAbelianScheme A) (hL : L.IsLB)
    (hs : s.IsGen) (hn : NormalizedCube s) (w x y v : T ⟶ A)
    (z : T.left) (J : (T.left ⟶ A.left) → L.ι) (hJ : Good L z J) :
    cubeValue s (w * x) y v z J * cubeValue s w x v z J =
      cubeValue s w (x * y) v z J * cubeValue s x y v z J := by
  let B := A ⊗ (A ⊗ (A ⊗ A))
  let a : B ⟶ A := fst _ _
  let b : B ⟶ A := snd _ _ ≫ fst _ _
  let c : B ⟶ A := snd _ _ ≫ snd _ _ ≫ fst _ _
  let d : B ⟶ A := snd _ _ ≫ snd _ _ ≫ snd _ _
  let e : 𝟙_ (Over S) ⟶ B := lift 1 (lift 1 (lift 1 1))
  let r : T ⟶ B := lift w (lift x (lift y v))
  letI : IsIso B.hom.appTop := (hA.tensor (hA.tensor (hA.tensor hA))).isIso_appTop
  have h : FormEq (Sum.elim (cubeFactors (a * b) c d) (cubeFactors a b d))
      (Sum.elim cubeExponent cubeExponent) (Sum.elim (cubeFactors a (b * c) d) (cubeFactors b c d))
      (Sum.elim cubeExponent cubeExponent) := by
    intro U _ k
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, cubeFactors, prod_cube]
    apply Additive.ofMul.injective
    simp only [_root_.mul_assoc, ofMul_mul, ofMul_inv]
    abel
  have ea : e ≫ a = 1 := lift_fst _ _
  have eb : e ≫ b = 1 := by simp [e, b]
  have ec : e ≫ c = 1 := by simp [e, c]
  have ed : e ≫ d = 1 := by simp [e, d]
  have eab : e ≫ (a * b) = 1 := by rw [MonObj.comp_mul, ea, eb, _root_.mul_one]
  have ebc : e ≫ (b * c) = 1 := by rw [MonObj.comp_mul, eb, ec, _root_.mul_one]
  have hEq := normalized_values_eq hL h B.hom e.left (Over.w e)
    (mulGen_isGen (cubePull_isGen hs (a * b) c d) (cubePull_isGen hs a b d))
    (mulGen_isGen (cubePull_isGen hs a (b * c) d) (cubePull_isGen hs b c d))
    (fun p K hK => ((val_mul hK _ _ e.left).trans
      (congrArg₂ (· * ·) (cubePull_at_identity hn (a * b) c d e eab ec ed p K hK)
        (cubePull_at_identity hn a b d e ea eb ed p K hK))).trans
      ((val_mul hK _ _ e.left).trans
        (congrArg₂ (· * ·) (cubePull_at_identity hn a (b * c) d e ea ebc ed p K hK)
          (cubePull_at_identity hn b c d e eb ec ed p K hK))).symm) r.left z J hJ
  have ra : r ≫ a = w := lift_fst _ _
  have rb : r ≫ b = x := by simp [r, b]
  have rc : r ≫ c = y := by simp [r, c]
  have rd : r ≫ d = v := by simp [r, d]
  rw [val_mul hJ, val_mul hJ, cubePull_value s (a * b) c d r z J hJ, cubePull_value s a b d r z J hJ,
    cubePull_value s a (b * c) d r z J hJ, cubePull_value s b c d r z J hJ, MonObj.comp_mul r a b,
    MonObj.comp_mul r b c, ra, rb, rc, rd] at hEq
  exact hEq

/-- An identity-normalized generator of the cube gives a cubical cocycle on test points. -/
theorem isCubicalCocycle_cubeValue {s : (cubeBundle A L).Gen} (hA : IsAbelianScheme A)
    (hL : L.IsLB) (hs : s.IsGen) (hn : NormalizedCube s)
    (z : T.left) (J : (T.left ⟶ A.left) → L.ι) (hJ : Good L z J) :
    IsCubicalCocycle (fun x y v : T ⟶ A => cubeValue s x y v z J) := by
  let B := A ⊗ (A ⊗ A)
  let a : B ⟶ A := fst _ _
  let b : B ⟶ A := snd _ _ ≫ fst _ _
  let c : B ⟶ A := snd _ _ ≫ snd _ _
  let e : 𝟙_ (Over S) ⟶ B := lift 1 (lift 1 1)
  letI : IsIso B.hom.appTop := (hA.tensor (hA.tensor hA)).isIso_appTop
  have ea : e ≫ a = 1 := lift_fst _ _
  have eb : e ≫ b = 1 := by simp [e, b]
  have ec : e ≫ c = 1 := by simp [e, c]
  have h₁ : FormEq (cubeFactors a b c) cubeExponent (cubeFactors b a c) cubeExponent := by
    intro U _ k
    simp only [cubeFactors, prod_cube, show b * a = a * b from mul_comm b a]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have h₂ : FormEq (cubeFactors a b c) cubeExponent (cubeFactors a c b) cubeExponent := by
    intro U _ k
    simp only [cubeFactors, prod_cube, show a * c * b = a * b * c from mul_right_comm a c b,
      show c * b = b * c from mul_comm c b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  refine ⟨fun x y => cubeValue_face hA hL hs hn x y z J hJ, ?_, ?_,
    fun w x y v => cubeValue_cocycle hA hL hs hn w x y v z J hJ⟩
  · intro x y v
    let r : T ⟶ B := lift x (lift y v)
    simpa only [r, a, b, c, Category.assoc, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using
      cubeValue_eq_of_formEq hL hs hn e a b c b a c ea eb ec eb ea ec h₁ r z J hJ
  · intro x y v
    let r : T ⟶ B := lift x (lift y v)
    simpa only [r, a, b, c, Category.assoc, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using
      cubeValue_eq_of_formEq hL hs hn e a b c a c b ea eb ec ea ec eb h₂ r z J hJ

end GlobalTheory.AbLaw.Cube
