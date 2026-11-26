import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.KernelInvariantSectionDescent
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalSectionModule

/-! A section in a character weight space descends after division by a generator
with the same character. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlatDescent GlobalTheory.MulSplit

variable {X Y B : Scheme.{0}} {L : LB X} {p : Y ⟶ B} {G : Type}

/-- Pullback on sections is injective when functions descend uniquely on every chart. -/
theorem GlobalTheory.FlatDescent.Descends.injective (hL : L.IsLB) {q : Y ⟶ Y} {τ : G → (Y ⟶ Y)} (H : Descends q τ) (hq : q ≫ p = p)
    {D : (Y ⟶ X) →₀ ℤ} {v : Vals L p} (hv : v ∈ Sg L p D) (h : pl L q hq v = 0) : v = 0 := by
  obtain ⟨s, rfl⟩ := hv
  refine ev_zero fun j => H.1 _ (fn_ext fun y hy => ?_)
  choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
  have h0 : sval s (𝟙 Y ≫ q) y I = 0 := congrFun h ⟨(y, I, 𝟙 Y), hI, Category.id_comp _⟩
  refine (gs_pull (𝟙 Y) q y _ hy _).trans ((sec_trans s (𝟙 Y ≫ q) y hy (Good.mem hI _ _)).trans ?_)
  refine ((congrArg _ h0).trans (mul_zero _)).trans (Eq.symm ?_)
  exact (gs_pull (𝟙 Y) q y _ hy _).trans ((gs_eq _ _ _ hy _).trans
    ((congrArg _ (map_zero _)).trans (map_zero _)))

private theorem GlobalTheory.FlatDescent.Descends.exists_mem (hL : L.IsLB) {q : Y ⟶ Y} {τ : G → (Y ⟶ Y)}
    (H : Descends q τ) (hq : q ≫ p = p) (hτ : ∀ g, τ g ≫ p = p)
    (hτq : ∀ g, τ g ≫ q = q) {D : (Y ⟶ X) →₀ ℤ} {v : Vals L p}
    (hv : v ∈ Sg L p (D.mapDomain (q ≫ ·))) (h : ∀ g, pl L (τ g) (hτ g) v = v) :
    ∃ w ∈ Sg L p D, pl L q hq w = v := by
  let f : D.support → (Y ⟶ X) := fun k => k.1
  let d : D.support → ℤ := fun k => D k.1
  have hd : dv (fun k => q ≫ f k) d = D.mapDomain (q ≫ ·) := by
    rw [dv_comp, dv_support]
  obtain ⟨s, rfl⟩ := (mem_Sg hL hd v).1 hv
  obtain ⟨t, ht⟩ := H.section hτq hL f d s (fun g y J hJ => by
    have e := congrFun (h g) ⟨(y, J, 𝟙 Y), hJ, Category.id_comp _⟩
    change sval s (𝟙 Y ≫ τ g) y J = sval s (𝟙 Y) y J at e
    simpa only [Category.id_comp] using e)
  exact ⟨ev p t, ⟨t, rfl⟩, funext fun i => ht _ _ _ i.2.1⟩

/-- Dividing a character eigenvector by a generator of that weight makes it invariant.
Invariant sections descend to the base. -/
theorem GlobalTheory.FlatDescent.Descends.weight (hL : L.IsLB) {q : Y ⟶ Y} {τ : G → (Y ⟶ Y)} (H : Descends q τ) (hq : q ≫ p = p)
    (hτ : ∀ g, τ g ≫ p = p) (hτq : ∀ g, τ g ≫ q = q) {D E F : (Y ⟶ X) →₀ ℤ} {u : (Vals L p)ˣ} (hu : IsG E u)
    (χ : G → Γ(B, ⊤)ˣ) (hχ : ∀ g, pl L (τ g) (hτ g) u.val = (χ g).val • u.val)
    (hF : D.mapDomain (q ≫ ·) + E = F) :
    ∃ f : Sg L p D →ₗ[Γ(B, ⊤)] Vals L p, Function.Injective f ∧
      ∀ v, (∃ x, f x = v) ↔ v ∈ Sg L p F ∧ ∀ g, pl L (τ g) (hτ g) v = (χ g).val • v := by
  refine ⟨⟨⟨fun x => pl L q hq x.1 * u.val, fun x y => ?_⟩, fun c x => ?_⟩, ?_, fun v => ⟨?_, ?_⟩⟩
  · rw [Submodule.coe_add, map_add, add_mul]
  · show pl L q hq (c • x.1) * u.val = c • (pl L q hq x.1 * u.val)
    rw [map_smul, smul_mul_assoc]
  · rw [injective_iff_map_eq_zero]
    intro x hx
    exact Subtype.ext (H.injective hL hq x.2 (u.mul_left_eq_zero.1 hx))
  · rintro ⟨x, rfl⟩
    refine ⟨mul_mem_Sg hL (pl_mem_Sg hL hq x.2 rfl) hu.1 hF, fun g => ?_⟩
    show pl L (τ g) (hτ g) (pl L q hq x.1 * u.val) = (χ g).val • (pl L q hq x.1 * u.val)
    rw [map_mul, hχ, pl_pl _ _ hq (hτq g), mul_smul_comm]
  · rintro ⟨hv, hv'⟩
    obtain ⟨w, hw, e⟩ := H.exists_mem hL hq hτ hτq (D := D) (v := v * (u⁻¹).val)
      (mul_mem_Sg hL hv hu.2 (by rw [← hF]; abel)) (fun g => by
        have h1 : pl L (τ g) (hτ g) (v * (u⁻¹).val) * pl L (τ g) (hτ g) u.val = pl L (τ g) (hτ g) v := by
          rw [← map_mul, Units.inv_mul_cancel_right]
        rw [hχ, hv', mul_smul_comm] at h1
        have h2 := congrArg (fun t => ((χ g)⁻¹).val • t) h1
        simp only [smul_smul, Units.inv_mul, one_smul] at h2
        exact (Units.eq_mul_inv_iff_mul_eq u).2 h2)
    refine ⟨⟨w, hw⟩, ?_⟩
    show pl L q hq w * u.val = v
    rw [e, Units.inv_mul_cancel_right]
