import GaloisForLFunctions.HTGeometry.MeromorphicPlaneField

/-!
# Meromorphic fields on connected open domains

The codiscrete construction used for the plane extends to every nonempty
connected open complex domain. It contains all meromorphic representatives,
has a faithful restriction map from the actual global plane field, and turns
a meromorphic square root of an analytic function into an analytic root
throughout the domain. Equality is tested near every point of the domain.
-/

open Filter Topology
namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- An actual nonempty connected open subset of the complex plane. -/
structure MeromorphicDomainData where
  carrier : Set ℂ
  isOpen : IsOpen carrier
  isPreconnected : IsPreconnected carrier
  nonempty : carrier.Nonempty

namespace MeromorphicDomainData

variable (D : MeromorphicDomainData)

abbrev codiscrete : Filter ℂ := Filter.codiscreteWithin D.carrier

theorem mem_codiscrete {S : Set ℂ} :
    S ∈ D.codiscrete ↔ ∀ z ∈ D.carrier, S ∈ 𝓝[≠] z := by
  constructor
  · intro h z hz
    have hu := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp h z hz
    have hd : D.carrier ∈ 𝓝[≠] z := nhdsWithin_le_nhds (D.isOpen.mem_nhds hz)
    filter_upwards [hu, hd] with w hw hwd
    exact hw.resolve_right (not_not.mpr hwd)
  · intro h
    apply mem_codiscreteWithin_iff_forall_mem_nhdsNE.mpr
    intro z hz
    exact Filter.mem_of_superset (h z hz) (fun _ hw => Or.inl hw)

/-- Meromorphic functions modulo punctured-neighbourhood equality throughout D. -/
def meromorphicSubring : Subring (Germ D.codiscrete ℂ) where
  carrier := {g | ∃ f : ℂ → ℂ, MeromorphicOn f D.carrier ∧ (f : Germ D.codiscrete ℂ) = g}
  zero_mem' := ⟨0, fun z _ => MeromorphicAt.const 0 z, rfl⟩
  one_mem' := ⟨1, fun z _ => MeromorphicAt.const 1 z, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, fun z hz => (hf z hz).add (hg z hz), rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, fun z hz => (hf z hz).mul (hg z hz), rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, fun z hz => (hf z hz).neg, rfl⟩

private theorem exists_inv {g : Germ D.codiscrete ℂ}
    (hg : g ∈ D.meromorphicSubring) (hne : g ≠ 0) :
    ∃ h ∈ D.meromorphicSubring, g * h = 1 := by
  obtain ⟨f, hf, rfl⟩ := hg
  have hnetop : ∀ z ∈ D.carrier, meromorphicOrderAt f z ≠ ⊤ := by
    intro z hz htop
    apply hne
    have hall : ∀ x ∈ D.carrier, meromorphicOrderAt f x = ⊤ := by
      intro x hx
      by_contra hn
      exact absurd htop (hf.meromorphicOrderAt_ne_top_of_isPreconnected
        D.isPreconnected hx hz hn)
    change (f : Germ D.codiscrete ℂ) = ((0 : ℂ → ℂ) : Germ D.codiscrete ℂ)
    exact Germ.coe_eq.mpr (D.mem_codiscrete.mpr fun x hx =>
      meromorphicOrderAt_eq_top_iff.mp (hall x hx))
  refine ⟨(f⁻¹ : ℂ → ℂ), ⟨f⁻¹, fun z hz => (hf z hz).inv, rfl⟩, ?_⟩
  have hn : ∀ᶠ z in D.codiscrete, f z ≠ 0 := D.mem_codiscrete.mpr fun z hz =>
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf z hz)).mp (hnetop z hz)
  apply Germ.coe_eq.mpr
  filter_upwards [hn] with z hz
  exact mul_inv_cancel₀ hz

private theorem one_ne_zero_germ :
    ((1 : ℂ → ℂ) : Germ D.codiscrete ℂ) ≠ ((0 : ℂ → ℂ) : Germ D.codiscrete ℂ) := by
  intro h
  obtain ⟨z, hz⟩ := D.nonempty
  have he : (1 : ℂ → ℂ) =ᶠ[𝓝[≠] z] (0 : ℂ → ℂ) :=
    D.mem_codiscrete.mp (Germ.coe_eq.mp h) z hz
  obtain ⟨w, hw⟩ := he.exists
  exact one_ne_zero hw

/-- The field of all meromorphic functions on D, not a single local germ field. -/
def Field : Type := D.meromorphicSubring

noncomputable instance : CommRing D.Field := inferInstanceAs (CommRing D.meromorphicSubring)

private theorem isField : IsField D.Field := by
  refine ⟨⟨0, 1, ?_⟩, mul_comm, ?_⟩
  · intro h
    exact D.one_ne_zero_germ (congrArg Subtype.val h).symm
  · intro x hne
    have hn : (show (D.meromorphicSubring : Type) from x).1 ≠ 0 := by
      intro h
      exact hne (Subtype.ext h)
    obtain ⟨h, hh, hxh⟩ := D.exists_inv (show (D.meromorphicSubring : Type) from x).2 hn
    exact ⟨show D.Field from ⟨h, hh⟩, Subtype.ext hxh⟩

noncomputable instance : _root_.Field D.Field := D.isField.toField

def germ (x : D.Field) : Germ D.codiscrete ℂ :=
  (show (D.meromorphicSubring : Type) from x).1

theorem germ_injective : Function.Injective D.germ := fun _ _ h => Subtype.ext h

noncomputable def ofMeromorphic (f : ℂ → ℂ) (hf : MeromorphicOn f D.carrier) : D.Field :=
  show D.Field from ⟨(f : Germ D.codiscrete ℂ), ⟨f, hf, rfl⟩⟩

theorem exists_rep (x : D.Field) :
    ∃ (f : ℂ → ℂ) (hf : MeromorphicOn f D.carrier), x = D.ofMeromorphic f hf := by
  obtain ⟨f, hf, he⟩ := (show (D.meromorphicSubring : Type) from x).2
  exact ⟨f, hf, Subtype.ext he.symm⟩

theorem ofMeromorphic_eq_iff {f g : ℂ → ℂ} (hf : MeromorphicOn f D.carrier)
    (hg : MeromorphicOn g D.carrier) :
    D.ofMeromorphic f hf = D.ofMeromorphic g hg ↔
      ∀ z ∈ D.carrier, f =ᶠ[𝓝[≠] z] g := by
  constructor
  · intro h
    exact D.mem_codiscrete.mp (Germ.coe_eq.mp (congrArg D.germ h))
  · intro h
    exact Subtype.ext (Germ.coe_eq.mpr (D.mem_codiscrete.mpr h))

private def restrictGerm : Germ planeCodiscrete ℂ →+* Germ D.codiscrete ℂ where
  toFun a := a.compTendsto id (by
    simpa only [Filter.Tendsto, Filter.map_id] using
      (Filter.codiscreteWithin_mono (Set.subset_univ D.carrier)))
  map_one' := by rw [← Germ.coe_one, Germ.coe_compTendsto]; rfl
  map_zero' := by rw [← Germ.coe_zero, Germ.coe_compTendsto]; rfl
  map_mul' a b := by
    induction a using Germ.inductionOn with
    | _ f => induction b using Germ.inductionOn with
      | _ g => simp only [← Germ.coe_mul, Germ.coe_compTendsto]; rfl
  map_add' a b := by
    induction a using Germ.inductionOn with
    | _ f => induction b using Germ.inductionOn with
      | _ g => simp only [← Germ.coe_add, Germ.coe_compTendsto]; rfl

/-- Faithful analytic restriction of the actual global meromorphic field. -/
noncomputable def restrictPlane : MeromorphicPlane →+* D.Field where
  toFun a := ⟨D.restrictGerm a.germ, by
    obtain ⟨f, hf, rfl⟩ := MeromorphicPlane.exists_rep a
    exact ⟨f, fun z _ => hf z, rfl⟩⟩
  map_one' := Subtype.ext D.restrictGerm.map_one
  map_zero' := Subtype.ext D.restrictGerm.map_zero
  map_add' a b := Subtype.ext (D.restrictGerm.map_add a.germ b.germ)
  map_mul' a b := Subtype.ext (D.restrictGerm.map_mul a.germ b.germ)

theorem restrictPlane_injective : Function.Injective D.restrictPlane :=
  D.restrictPlane.injective

@[simp] theorem restrictPlane_ofMeromorphic (f : ℂ → ℂ) (hf : ∀ z, MeromorphicAt f z) :
    D.restrictPlane (HTGeometry.ofMeromorphic f hf) = D.ofMeromorphic f (fun z _ => hf z) := rfl

noncomputable instance : Algebra MeromorphicPlane D.Field := D.restrictPlane.toAlgebra

@[simp] theorem ofMeromorphic_mul {f g : ℂ → ℂ} (hf : MeromorphicOn f D.carrier)
    (hg : MeromorphicOn g D.carrier) :
    D.ofMeromorphic f hf * D.ofMeromorphic g hg =
      D.ofMeromorphic (f * g) (fun z hz => (hf z hz).mul (hg z hz)) := rfl

@[simp] theorem ofMeromorphic_one :
    D.ofMeromorphic 1 (fun z _ => MeromorphicAt.const 1 z) = 1 := rfl

end MeromorphicDomainData
end
end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry.MeromorphicDomainData
open Filter Topology

/-- A meromorphic square of an analytic function has an analytic root throughout the domain. -/
theorem analytic_sqrt_of_isSquare (D : MeromorphicDomainData) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f D.carrier)
    (hsq : IsSquare (D.ofMeromorphic f (fun z hz => (hf z hz).meromorphicAt))) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g D.carrier ∧ ∀ z ∈ D.carrier, g z ^ 2 = f z := by
  obtain ⟨a, ha⟩ := hsq
  obtain ⟨g, hg, rfl⟩ := D.exists_rep a
  have heq : ∀ z ∈ D.carrier, f =ᶠ[𝓝[≠] z] (fun w => g w ^ 2) := by
    apply (D.ofMeromorphic_eq_iff (fun z hz => (hf z hz).meromorphicAt)
      (fun z hz => (hg z hz).pow 2)).mp
    apply ha.trans
    rw [D.ofMeromorphic_mul]
    apply (D.ofMeromorphic_eq_iff _ _).mpr
    intro z _
    exact Filter.Eventually.of_forall fun w => (pow_two (g w)).symm
  let h := toMeromorphicNFOn g D.carrier
  have hheq (z : ℂ) (hz : z ∈ D.carrier) : h =ᶠ[𝓝[≠] z] g :=
    hg.toMeromorphicNFOn_eq_self_on_nhdsNE hz
  have han (z : ℂ) (hz : z ∈ D.carrier) : AnalyticAt ℂ h z := by
    apply ((meromorphicNFOn_toMeromorphicNFOn g D.carrier) hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hg hz]
    have hord := (hf z hz).meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_congr (heq z hz)] at hord
    change 0 ≤ meromorphicOrderAt (g ^ 2) z at hord
    rw [meromorphicOrderAt_pow (hg z hz)] at hord
    cases hx : meromorphicOrderAt g z with
    | top => simp
    | coe n =>
      rw [hx] at hord
      change (↑(0 : ℤ) : WithTop ℤ) ≤ ↑((2 : ℤ) * n) at hord
      have hn : (0 : ℤ) ≤ 2 * n := WithTop.coe_le_coe.mp hord
      norm_cast
      omega
  refine ⟨h, han, fun z hz => ?_⟩
  have he : (fun w => h w ^ 2) =ᶠ[𝓝[≠] z] f := by
    filter_upwards [hheq z hz, heq z hz] with w hw hfw
    rw [hw, ← hfw]
  exact ((ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    ((han z hz).continuousAt.pow 2) (hf z hz).continuousAt).mp he).eq_of_nhds

end GaloisForLFunctions.HTGeometry.MeromorphicDomainData
