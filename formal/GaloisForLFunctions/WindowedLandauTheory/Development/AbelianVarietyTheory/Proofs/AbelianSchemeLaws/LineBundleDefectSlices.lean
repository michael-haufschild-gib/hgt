import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.SquareZeroLineBundleObstruction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.RelativeFormsPullback

/-! On a slice with a trivialization, dividing the lifted units removes the transition
functions from their overlap equations. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.SchemeCohomology GlobalTheory.LineBundleSections

namespace GlobalTheory.AbLaw.SmallExtension

variable {R : Type} [CommRing R] {X T : Scheme.{0}} {L : LB X}
  {p : X ⟶ Spec (CommRingCat.of R)} {ε : R}
  {I : Type} {W : I → X.Opens} {c : I → L.ι} {hle : ∀ i, W i ≤ L.U (c i)}
  {u : ∀ i, Γ(X, W i)} {α : ∀ i j, Γ(X, W i ⊓ W j)}

private theorem div_coordinates {A : Type} [CommRing A] {u v g a b a' b' x : A}
    (hu : u = g * v * x) (ht : a = g * b) (ha : a * a' = 1) (hb : b * b' = 1) :
    u * a' = v * b' * x := by
  rw [ht] at ha
  linear_combination (v * x * b') * ha - (g * v * x * a') * hb + a' * hu

/-- Comparing each lifted unit with a trivialization on the slice leaves only the
infinitesimal factor in the overlap relation. -/
theorem LiftDefect.exists_units_on_slice
    (h : LiftDefect (p := p) (ε := ε) W c hle u α) (hu : ∀ i, IsUnit (u i))
    (a : T ⟶ X) (t : (L.pull a).Gen) (ht : t.IsGen) :
    ∃ r : ∀ i, Γ(T, a ⁻¹ᵁ W i), (∀ i, IsUnit (r i)) ∧
      ∀ i j,
        let V := a ⁻¹ᵁ W i ⊓ a ⁻¹ᵁ W j
        letI := sectionAlgebra (a ≫ p) V
        resG T inf_le_left (r i) = resG T inf_le_right (r j) *
          (1 + algebraMap R Γ(T, V) ε * a.appLE (W i ⊓ W j) V (fun _ hx => hx) (α i j)) := by
  let hW (i : I) : a ⁻¹ᵁ W i ≤ (L.pull a).U (fun _ => c i) :=
    (a.preimage_mono (hle i)).trans (pull_chart L a (c i)).ge
  let v (i : I) := t.s (fun _ => c i)
  let r (i : I) : Γ(T, a ⁻¹ᵁ W i) := a.app (W i) (u i) * resG T (hW i) ((v i)⁻¹).val
  have hr (i : I) : IsUnit (r i) :=
    ((hu i).map (a.app (W i)).hom).mul (((v i)⁻¹).isUnit.map (resG T (hW i)))
  refine ⟨r, hr, fun i j => ?_⟩
  let V := a ⁻¹ᵁ W i ⊓ a ⁻¹ᵁ W j
  let O := W i ⊓ W j
  letI := sectionAlgebra (a ≫ p) V
  have hi : V ≤ a ⁻¹ᵁ W i := inf_le_left
  have hj : V ≤ a ⁻¹ᵁ W j := inf_le_right
  let b : SectionRing p O →ₐ[R] SectionRing (a ≫ p) V :=
    (sectionRes (a ≫ p) (homOfLE (show V ≤ a ⁻¹ᵁ O from fun _ hx => hx))).comp
      (sectionPullback (f := a) rfl O)
  have hb := b.commutes ε
  change a.appLE O V _ (algebraMap R (SectionRing p O) ε) = _ at hb
  have e := congrArg (a.appLE O V (fun _ hx => hx)).hom (h i j)
  simp only [map_mul, map_add, map_one, appLE_resG, hb] at e
  have htij := pulledGenerator_compat ht (hi.trans (a.preimage_mono (hle i)))
    (hj.trans (a.preimage_mono (hle j)))
  have hprod (k : I) (hk : V ≤ a ⁻¹ᵁ W k) :
      resG T (hk.trans (hW k)) (v k).val * resG T (hk.trans (hW k)) ((v k)⁻¹).val = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  simp only [r, map_mul, resG_resG, Scheme.Hom.app_eq_appLE, resG_appLE]
  exact div_coordinates e htij (hprod i hi) (hprod j hj)

private theorem restrict_scalar {S : Type} [CommRing S] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (CommRingCat.of S)) {U V : Y.Opens} (h : V ≤ U) (c : S) :
    letI := sectionAlgebra f U
    letI := sectionAlgebra f V
    resG Y h (algebraMap S Γ(Y, U) c) = algebraMap S Γ(Y, V) c :=
  (sectionRes f (homOfLE h)).commutes c

private theorem defect_of_normalization {A : Type} [CommRing A] {e x y a b d c : A}
    (hy : IsUnit y) (he : e * e = 0) (hxy : x = y * (1 + e * a))
    (hx : x * (1 - e * b) = c) (hy' : y * (1 - e * d) = c) :
    e * (a - (b - d)) = 0 := by
  have h : y * ((1 + e * a) * (1 - e * b) - (1 - e * d)) = 0 := by
    rw [mul_sub, ← mul_assoc, ← hxy, hx, hy', sub_self]
  have h' := hy.mul_right_eq_zero.1 h
  linear_combination h' + (a * b) * he

/-- If the slice has only scalar functions after reduction, its additive defect is a
coboundary after multiplication by the square-zero parameter. -/
theorem LiftDefect.coboundary_on_slice
    (h : LiftDefect (p := p) (ε := ε) W c hle u α) (hu : ∀ i, IsUnit (u i))
    (hε : ε * ε = 0) (hc : ⨆ i, W i = ⊤) (haff : ∀ i, IsAffineOpen (W i))
    (a : T ⟶ X) [IsAffineHom a] (t : (L.pull a).Gen) (ht : t.IsGen)
    {T' : Scheme.{0}} {π : T' ⟶ T} {f : T' ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))}
    (H : IsPullback π f (a ≫ p) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))))
    (hΓ : Function.Surjective f.appTop) :
    ∃ β : ∀ i, Γ(T, a ⁻¹ᵁ W i),
      ∀ i j,
        let V := a ⁻¹ᵁ W i ⊓ a ⁻¹ᵁ W j
        letI := sectionAlgebra (a ≫ p) V
        algebraMap R Γ(T, V) ε *
          (a.appLE (W i ⊓ W j) V (fun _ hx => hx) (α i j) -
            (resG T inf_le_left (β i) - resG T inf_le_right (β j))) = 0 := by
  obtain ⟨r, hr, hrel⟩ := h.exists_units_on_slice hu a t ht
  let V (i : I) := a ⁻¹ᵁ W i
  let Q := R ⧸ Ideal.span {ε}
  have e0 : algebraMap R Q ε = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ε)
  have hcov : ⨆ i, π ⁻¹ᵁ V i = ⊤ := π.iSup_preimage_eq_top (a.iSup_preimage_eq_top hc)
  have hcompat (i j : I) :
      resG T' inf_le_left (π.app (V i) (r i)) = resG T' inf_le_right (π.app (V j) (r j)) := by
    let O := V i ⊓ V j
    have e := congrArg (π.appLE O (π ⁻¹ᵁ V i ⊓ π ⁻¹ᵁ V j) (fun _ hx => hx)).hom (hrel i j)
    simp only [map_mul, map_add, map_one, appLE_resG, appLE_base_algebraMap H.w, e0, map_zero,
      zero_mul, add_zero, mul_one] at e
    simp only [Scheme.Hom.app_eq_appLE, resG_appLE]
    exact e
  obtain ⟨b, hb⟩ := exists_fun_of_cover (fun i => π ⁻¹ᵁ V i) (fun _ => le_top) hcov.ge
    (fun i => π.app (V i) (r i)) hcompat
  obtain ⟨b', rfl⟩ := hΓ b
  obtain ⟨c', rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of Q)).inv).2 b'
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
  have hb' (i : I) :
      letI := sectionAlgebra f (π ⁻¹ᵁ V i)
      algebraMap Q Γ(T', π ⁻¹ᵁ V i) (algebraMap R Q c) = π.app (V i) (r i) := by
    have e : f.appLE ⊤ ⊤ le_top = f.appTop := by
      simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.preimage_top]
    have hbi := hb i
    rw [← e] at hbi
    letI := sectionAlgebra f ⊤
    change resG T' le_top (algebraMap Q Γ(T', ⊤) (algebraMap R Q c)) =
      π.app (V i) (r i) at hbi
    rw [← restrict_scalar f (le_top : π ⁻¹ᵁ V i ≤ ⊤)]
    exact hbi
  have key (i : I) :
      letI := sectionAlgebra (a ≫ p) (V i)
      ∃ β : Γ(T, V i), r i * (1 - algebraMap R Γ(T, V i) ε * β) =
        algebraMap R Γ(T, V i) c := by
    letI := sectionAlgebra (a ≫ p) (V i)
    let e := algebraMap R Γ(T, V i) ε
    let c₀ := algebraMap R Γ(T, V i) c
    have hz : π.app (V i) (r i - c₀) = 0 := by
      rw [map_sub, sub_eq_zero, Scheme.Hom.app_eq_appLE]
      have hbi := hb' i
      rw [Scheme.Hom.app_eq_appLE] at hbi
      exact hbi.symm.trans (appLE_base_algebraMap H.w le_rfl c).symm
    obtain ⟨d, hd⟩ := exists_eq_mul_of_app_eq_zero H ((haff i).preimage a) hz
    obtain ⟨w, hw⟩ := (hr i).exists_right_inv
    change r i - c₀ = e * d at hd
    exact ⟨w * d, by linear_combination hd - (e * d) * hw⟩
  choose β hβ using key
  refine ⟨β, fun i j => ?_⟩
  let O := V i ⊓ V j
  letI := sectionAlgebra (a ≫ p) O
  let e := algebraMap R Γ(T, O) ε
  have he : e * e = 0 := by rw [← map_mul, hε, map_zero]
  have h1 := congrArg (resG T (inf_le_left : O ≤ V i)) (hβ i)
  have h2 := congrArg (resG T (inf_le_right : O ≤ V j)) (hβ j)
  simp only [map_mul, map_sub, map_one, restrict_scalar] at h1 h2
  exact defect_of_normalization ((hr j).map (resG T inf_le_right)) he (hrel i j) h1 h2

end GlobalTheory.AbLaw.SmallExtension
