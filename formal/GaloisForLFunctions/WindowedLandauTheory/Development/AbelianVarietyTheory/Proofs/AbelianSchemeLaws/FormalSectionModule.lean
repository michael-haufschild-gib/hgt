import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalSectionOperations
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalPullbackGeneratorOperations
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Sections of formal products of pullbacks as submodules of a common ring of germs. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.MulSplit

variable {Y : Scheme.{0}} in
private def secAdd {M : LB Y} (s t : LB.Sec M) : LB.Sec M where
  f i := s.f i + t.f i
  compat i j := by rw [map_add, map_add, s.compat, t.compat, mul_add]

section
variable {Y : Scheme.{0}}
private def secZero (M : LB Y) : LB.Sec M where
  f _ := 0
  compat _ _ := by rw [map_zero, map_zero, mul_zero]

private def secCMul {M : LB Y} {V : Y.Opens} (hV : ∀ i, M.U i ≤ V) (c : Γ(Y, V)) (s : LB.Sec M) : LB.Sec M where
  f i := (Y.presheaf.map (homOfLE (hV i)).op).hom c * s.f i
  compat i j := fn_ext fun y hy => by
    have e := congrArg (gs (𝟙 Y) y (M.U i ⊓ M.U j)) (s.compat i j)
    rw [gs_res (𝟙 Y) y inf_le_left hy, gs_mul (𝟙 Y) y _ hy, gs_res (𝟙 Y) y inf_le_right hy] at e
    rw [gs_res (𝟙 Y) y inf_le_left hy, gs_mul (𝟙 Y) y _ hy.1, gs_res (𝟙 Y) y (hV i) hy.1, e,
      gs_mul (𝟙 Y) y _ hy, gs_res (𝟙 Y) y inf_le_right hy, gs_mul (𝟙 Y) y _ hy.2, gs_res (𝟙 Y) y (hV j) hy.2]
    ac_rfl

end

variable {X Y B : Scheme.{0}} (L : LB X) (p : Y ⟶ B)

/-- A point with compatible chart choices and an endomorphism over the base. -/
def Idx : Type :=
  {t : Y × ((Y ⟶ X) → L.ι) × (Y ⟶ Y) // Good L t.1 t.2.1 ∧ t.2.2 ≫ p = p}

/-- The common ring of germ values for all presentations of the line bundle. -/
def Vals : Type := ∀ i : Idx L p, Y.presheaf.stalk i.1.1

instance : CommRing (Vals L p) := inferInstanceAs (CommRing (∀ i : Idx L p, Y.presheaf.stalk i.1.1))

def cstHom : Γ(B, ⊤) →+* Vals L p :=
  RingHom.pi fun i => (Y.presheaf.germ (p ⁻¹ᵁ ⊤) i.1.1 trivial).hom.comp (p.app ⊤).hom

instance : Algebra Γ(B, ⊤) (Vals L p) := (cstHom L p).toAlgebra

variable {L p}

theorem algebraMap_vals (c : Γ(B, ⊤)) (i : Idx L p) :
    algebraMap Γ(B, ⊤) (Vals L p) c i = gs p i.1.1 ⊤ c := (gs_eq p i.1.1 ⊤ trivial c).symm

theorem mul_vals (v w : Vals L p) (i : Idx L p) : (v * w) i = v i * w i := rfl

variable {K K' : Type} [Fintype K] [Fintype K']

variable (p) in

/-- Evaluate a section at every point and compatible chart assignment. -/
def ev {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) : Vals L p :=
  fun i => sval s i.1.2.2 i.1.1 i.1.2.1

/-- The exponent sum of the formal pullback factors. -/
def dv (φ : K → (Y ⟶ X)) (ε : K → ℤ) : (Y ⟶ X) →₀ ℤ := ∑ k, Finsupp.single (φ k) (ε k)

theorem formEq_of_dv {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : dv φ ε = dv φ' ε') : FormEq φ ε φ' ε' := by
  intro U _ f
  have := congrArg (Finsupp.linearCombination ℤ (fun ψ => Additive.ofMul (f ψ))) h
  simp only [dv, map_sum, Finsupp.linearCombination_single] at this
  apply Additive.ofMul.injective
  simpa only [ofMul_prod, ofMul_zpow] using this

theorem dv_support (D : (Y ⟶ X) →₀ ℤ) : dv (fun k : D.support => k.1) (fun k => D k.1) = D :=
  (Finset.sum_coe_sort D.support (fun ψ => Finsupp.single ψ (D ψ))).trans D.sum_single

theorem dv_comp {Y' : Scheme.{0}} (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    dv (fun k => h ≫ φ k) ε = (dv φ ε).mapDomain (h ≫ ·) := by
  simp only [dv, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]

private theorem gs_add (r : Y ⟶ X) (y : Y) (U : X.Opens) (hy : r y ∈ U)
    (a b : Γ(X, U)) : gs r y U (a + b) = gs r y U a + gs r y U b := by
  simp only [gs_eq r y U hy, map_add]

theorem ev_add {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s t u : LB.Sec (LB.LinComb L φ ε)}
    (h : ∀ j, u.f j = s.f j + t.f j) : ev p u = ev p s + ev p t :=
  funext fun i => (congrArg (gs _ _ _) (h _)).trans (gs_add _ _ _ (i.2.1.mem φ _) _ _)

theorem ev_smul {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s u : LB.Sec (LB.LinComb L φ ε)} (c : Γ(B, ⊤))
    (h : ∀ j, u.f j = (Y.presheaf.map (homOfLE le_top).op).hom (p.appTop.hom c) * s.f j) :
    ev p u = c • ev p s := by
  funext i
  have hm := i.2.1.mem φ i.1.2.2
  refine (congrArg (gs _ _ _) (h _)).trans ((gs_mul _ _ _ hm _ _).trans ?_)
  rw [Algebra.smul_def, mul_vals, algebraMap_vals]
  refine congrArg₂ (· * ·) ((gs_res _ _ _ hm _).trans ((gs_pull _ p _ ⊤ trivial c).trans ?_)) rfl
  rw [i.2.2]

theorem ev_zero {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, s.f j = 0) :
    ev p s = 0 :=
  funext fun i => (congrArg (gs _ _ _) (h _)).trans ((gs_eq _ _ _ (i.2.1.mem φ _) _).trans
    ((congrArg _ (map_zero _)).trans (map_zero _)))

theorem ev_inj (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s t : LB.Sec (LB.LinComb L φ ε)}
    (h : ev p s = ev p t) (j : K → L.ι) : s.f j = t.f j :=
  sec_ext_val hL (fun y J hJ => congrFun h ⟨(y, J, 𝟙 Y), hJ, Category.id_comp _⟩) j

variable (L p) in

/-- The submodule of values of global sections in the given formal product. -/
def Sg (D : (Y ⟶ X) →₀ ℤ) : Submodule Γ(B, ⊤) (Vals L p) where
  carrier := {v | ∃ s : LB.Sec (LB.LinComb L (fun k : D.support => k.1) (fun k => D k.1)), ev p s = v}
  add_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨secAdd s t, ev_add fun _ => rfl⟩
  zero_mem' := ⟨secZero _, ev_zero fun _ => rfl⟩
  smul_mem' := by
    rintro c _ ⟨s, rfl⟩
    exact ⟨secCMul (fun _ => le_top) (p.appTop.hom c) s, ev_smul c fun _ => rfl⟩

theorem mem_Sg (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {D : (Y ⟶ X) →₀ ℤ} (h : dv φ ε = D)
    (v : Vals L p) : v ∈ Sg L p D ↔ ∃ s : LB.Sec (LB.LinComb L φ ε), ev p s = v := by
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨s', hs⟩ := exists_sec_of_formEq hL (formEq_of_dv ((dv_support D).trans h.symm)) s
    exact ⟨s', funext fun i => hs _ _ _ _ i.2.1⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨s', hs⟩ := exists_sec_of_formEq hL (formEq_of_dv (h.trans (dv_support D).symm)) s
    exact ⟨s', funext fun i => hs _ _ _ _ i.2.1⟩

theorem mul_mem_Sg (hL : L.IsLB) {D E F : (Y ⟶ X) →₀ ℤ} {v w : Vals L p} (hv : v ∈ Sg L p D)
    (hw : w ∈ Sg L p E) (h : D + E = F) : v * w ∈ Sg L p F := by
  obtain ⟨s, rfl⟩ := hv
  obtain ⟨t, rfl⟩ := hw
  refine (mem_Sg hL ?_ _).2 ⟨mulSec s t, funext fun i => sval_mulSec s t _ _ i.2.1⟩
  rw [← h]
  exact (Fintype.sum_sum_type _).trans (congrArg₂ (· + ·) (dv_support D) (dv_support E))

variable (L) in

/-- Pull back the chart values by precomposing the endomorphism over the base. -/
def pl (h : Y ⟶ Y) (hh : h ≫ p = p) : Vals L p →ₐ[Γ(B, ⊤)] Vals L p where
  toFun v := fun i => v ⟨(i.1.1, i.1.2.1, i.1.2.2 ≫ h), i.2.1, by rw [Category.assoc, hh, i.2.2]⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem pl_pl {h h' h'' : Y ⟶ Y} (hh : h ≫ p = p) (hh' : h' ≫ p = p) (hh'' : h'' ≫ p = p) (e : h ≫ h' = h'')
    (v : Vals L p) : pl L h hh (pl L h' hh' v) = pl L h'' hh'' v := by
  subst e
  funext i
  have : ∀ (a b : Y ⟶ Y) (ha hb), a = b → v ⟨(i.1.1, i.1.2.1, a), ha⟩ = v ⟨(i.1.1, i.1.2.1, b), hb⟩ := by
    rintro a b ha hb rfl; rfl
  exact this _ _ _ _ (Category.assoc _ _ _)

theorem pl_id {h : Y ⟶ Y} (hh : h ≫ p = p) (e : h = 𝟙 Y) (v : Vals L p) : pl L h hh v = v := by
  subst e
  funext i
  have : ∀ (a b : Y ⟶ Y) (ha hb), a = b → v ⟨(i.1.1, i.1.2.1, a), ha⟩ = v ⟨(i.1.1, i.1.2.1, b), hb⟩ := by
    rintro a b ha hb rfl; rfl
  exact this _ _ _ i.2 (Category.comp_id _)

theorem pl_mem_Sg (hL : L.IsLB) {h : Y ⟶ Y} (hh : h ≫ p = p) {D E : (Y ⟶ X) →₀ ℤ} {v : Vals L p}
    (hv : v ∈ Sg L p D) (e : D.mapDomain (h ≫ ·) = E) : pl L h hh v ∈ Sg L p E := by
  obtain ⟨s, rfl⟩ := hv
  refine (mem_Sg hL ?_ _).2 ⟨pullSec s h, funext fun i => sval_pullSec s h _ _ i.2.1⟩
  rw [dv_comp, dv_support, e]

/-- A unit gives a generator when it and its inverse are sections in opposite products. -/
def IsG (D : (Y ⟶ X) →₀ ℤ) (u : (Vals L p)ˣ) : Prop := u.val ∈ Sg L p D ∧ (u⁻¹).val ∈ Sg L p (-D)

theorem exists_isG (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ u : (Vals L p)ˣ, IsG (dv φ ε) u ∧ ∀ i : Idx L p, u.val i = (val t i.1.2.2 i.1.1 i.1.2.1).val := by
  refine ⟨⟨fun i => (val t i.1.2.2 i.1.1 i.1.2.1).val, fun i => ((val t i.1.2.2 i.1.1 i.1.2.1)⁻¹).val,
    funext fun i => Units.mul_inv _, funext fun i => Units.inv_mul _⟩, ⟨?_, ?_⟩, fun _ => rfl⟩
  · exact (mem_Sg hL rfl _).2 ⟨genSec t ht, funext fun i => sval_genSec t ht _ _ i.2.1⟩
  · refine (mem_Sg hL ?_ _).2 ⟨genSec (LB.invGen L φ ε t) (invGen_isGen ht), funext fun i =>
      (sval_genSec _ _ _ _ i.2.1).trans
        (congrArg Units.val (val_inv (s := t) i.1.2.2 i.1.1 i.1.2.1))⟩
    simp only [dv, Finsupp.single_neg, Finset.sum_neg_distrib]

theorem IsG.inv {D : (Y ⟶ X) →₀ ℤ} {u : (Vals L p)ˣ} (h : IsG D u) : IsG (-D) u⁻¹ :=
  ⟨h.2, by rw [inv_inv, neg_neg]; exact h.1⟩

theorem IsG.mul (hL : L.IsLB) {D E : (Y ⟶ X) →₀ ℤ} {u w : (Vals L p)ˣ} (h : IsG D u) (h' : IsG E w) :
    IsG (D + E) (u * w) :=
  ⟨mul_mem_Sg hL h.1 h'.1 rfl, by rw [mul_inv]; exact mul_mem_Sg hL h.2 h'.2 (neg_add _ _).symm⟩

theorem IsG.pow (hL : L.IsLB) {D : (Y ⟶ X) →₀ ℤ} {u : (Vals L p)ˣ} (h : IsG D u) (j : ℕ) :
    IsG ((j + 1) • D) (u ^ (j + 1)) := by
  induction j with
  | zero => simpa using h
  | succ j ih => rw [succ_nsmul, pow_succ]; exact ih.mul hL h

theorem IsG.pull (hL : L.IsLB) {h : Y ⟶ Y} (hh : h ≫ p = p) {D : (Y ⟶ X) →₀ ℤ} {u : (Vals L p)ˣ}
    (hu : IsG D u) : IsG (D.mapDomain (h ≫ ·)) (Units.map (pl L h hh : Vals L p →* Vals L p) u) :=
  ⟨pl_mem_Sg hL hh hu.1 rfl, pl_mem_Sg hL hh hu.2 (map_neg (Finsupp.mapDomain.addMonoidHom (h ≫ ·)) D)⟩

theorem IsG.equiv (hL : L.IsLB) {D E F : (Y ⟶ X) →₀ ℤ} {u : (Vals L p)ˣ} (hu : IsG D u) (h : E + D = F) :
    Nonempty (Sg L p E ≃ₗ[Γ(B, ⊤)] Sg L p F) :=
  ⟨{ toFun := fun v => ⟨v.1 * u.val, mul_mem_Sg hL v.2 hu.1 h⟩
     invFun := fun v => ⟨v.1 * (u⁻¹).val, mul_mem_Sg hL v.2 hu.2 (by rw [← h]; abel)⟩
     map_add' := fun _ _ => Subtype.ext (add_mul _ _ _)
     map_smul' := fun _ _ => Subtype.ext (smul_mul_assoc _ _ _)
     left_inv := fun _ => Subtype.ext (Units.mul_inv_cancel_right _ _)
     right_inv := fun _ => Subtype.ext (Units.inv_mul_cancel_right _ _) }⟩

theorem pl_equiv (hL : L.IsLB) {h h' : Y ⟶ Y} (hh : h ≫ p = p) (hh' : h' ≫ p = p) (e : h ≫ h' = 𝟙 Y)
    (e' : h' ≫ h = 𝟙 Y) {D E : (Y ⟶ X) →₀ ℤ} (hE : D.mapDomain (h ≫ ·) = E) :
    Nonempty (Sg L p D ≃ₗ[Γ(B, ⊤)] Sg L p E) :=
  ⟨{ toFun := fun v => ⟨pl L h hh v.1, pl_mem_Sg hL hh v.2 hE⟩
     invFun := fun v => ⟨pl L h' hh' v.1, pl_mem_Sg hL hh' v.2 (by
       rw [← hE, ← Finsupp.mapDomain_comp]
       refine (congrArg (Finsupp.mapDomain · D) (funext fun ψ => ?_)).trans Finsupp.mapDomain_id
       show h' ≫ h ≫ ψ = ψ
       rw [← Category.assoc, e', Category.id_comp])⟩
     map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
     map_smul' := fun _ _ => Subtype.ext (map_smul (pl L h hh) _ _)
     left_inv := fun _ => Subtype.ext ((pl_pl _ _ (Category.id_comp _) e' _).trans (pl_id _ rfl _))
     right_inv := fun _ => Subtype.ext ((pl_pl _ _ (Category.id_comp _) e _).trans (pl_id _ rfl _)) }⟩

end GlobalTheory.MulSplit
