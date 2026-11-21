import GaloisForLFunctions.WindowedLandauTheory.SatakeDualWeyl.StatementB

noncomputable section

open Matrix

namespace WindowedLandauTheory.UG.P

theorem glEquiv_apply' {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (g : GL n K) (x : n → K) : WindowedLandauTheory.UG.glEquiv g x = (g : Matrix n n K) *ᵥ x := by
  first
  | rfl
  | simp [LinearMap.GeneralLinearGroup.generalLinearEquiv, Matrix.GeneralLinearGroup.toLin, Matrix.toLin'_apply]

theorem hform_eq_dot {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x y : n → A) : WindowedLandauTheory.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  unfold WindowedLandauTheory.UG.hform
  first
  | simp only [dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]
  | simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J M : Matrix n n A) (x y : n → A) :
    WindowedLandauTheory.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = WindowedLandauTheory.UG.hform σ (WindowedLandauTheory.UG.cT σ M * J * M) x y := by
  rw [hform_eq_dot, hform_eq_dot]
  unfold WindowedLandauTheory.UG.cT
  have h1 : (⇑σ ∘ (M *ᵥ x)) = (M.map σ) *ᵥ (⇑σ ∘ x) := by
    funext i
    first
    | exact RingHom.map_mulVec σ M x i
    | simp [mulVec, dotProduct, map_sum, map_mul]
  rw [h1, mulVec_mulVec, ← vecMul_transpose (M.map ⇑σ) (⇑σ ∘ x), ← dotProduct_mulVec, mulVec_mulVec,
    Matrix.mul_assoc]

theorem hform_single {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (J : Matrix n n A) (i j : n) :
    WindowedLandauTheory.UG.hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  rw [hform_eq_dot]
  have hs : (⇑σ ∘ Pi.single i (1 : A)) = Pi.single i 1 := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [Pi.single_apply, hk]
  rw [hs]
  simp [mulVec_single]

theorem hform_gram {K : Type} [Field K] [StarRing K] {n : Type} [Fintype n] [DecidableEq n]
    (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K) (x y : n → K) :
    h x y = WindowedLandauTheory.UG.hform (starRingEnd K) (WindowedLandauTheory.UG.gram h) x y := by
  have hx : ∀ v : n → K, v = ∑ i, v i • (Pi.single i 1 : n → K) := by
    intro v
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx x, hx y]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    Finset.mul_sum]
  unfold WindowedLandauTheory.UG.hform WindowedLandauTheory.UG.gram
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [RingHom.id_apply]
  ring

theorem hermitian_lattice_correspondence_holds : WindowedLandauTheory.UG.HermBridge := by
  intro K _ _ n _ _ h g
  unfold WindowedLandauTheory.UG.UJ HermitianLatticesTheory.isom
  constructor
  · intro hg x y
    have hg' : WindowedLandauTheory.UG.cT (starRingEnd K) (g : Matrix n n K) * WindowedLandauTheory.UG.gram h * (g : Matrix n n K)
        = WindowedLandauTheory.UG.gram h := hg
    show h (WindowedLandauTheory.UG.glEquiv g x) (WindowedLandauTheory.UG.glEquiv g y) = h x y
    rw [glEquiv_apply', glEquiv_apply', hform_gram h ((g : Matrix n n K) *ᵥ x) ((g : Matrix n n K) *ᵥ y),
      hform_gram h x y, hform_mulVec, hg']
  · intro hg
    have hg' : ∀ x y : n → K, h (WindowedLandauTheory.UG.glEquiv g x) (WindowedLandauTheory.UG.glEquiv g y) = h x y := hg
    show WindowedLandauTheory.UG.cT (starRingEnd K) (g : Matrix n n K) * WindowedLandauTheory.UG.gram h * (g : Matrix n n K)
        = WindowedLandauTheory.UG.gram h
    ext i j
    have := hg' (Pi.single i 1) (Pi.single j 1)
    rw [glEquiv_apply', glEquiv_apply',
      hform_gram h ((g : Matrix n n K) *ᵥ Pi.single i 1) ((g : Matrix n n K) *ᵥ Pi.single j 1),
      hform_gram h (Pi.single i 1) (Pi.single j 1), hform_mulVec, hform_single, hform_single] at this
    exact this

theorem hermitian_correspondence_surjective_holds : WindowedLandauTheory.UG.HermBridgeSurj := by
  intro K _ _ n _ _ h u _
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K)).symm u), ?_⟩
  unfold WindowedLandauTheory.UG.glEquiv
  simp

theorem stabilizer_group_map_holds : WindowedLandauTheory.UG.StabGmap := by
  intro K _ R _ _ n _ _ Λ g
  unfold WindowedLandauTheory.UG.stabGL HermitianLatticesTheory.gmap
  show (∀ x : n → K, x ∈ Λ ↔ (g : Matrix n n K) *ᵥ x ∈ Λ) ↔ _
  constructor
  · intro hg
    ext y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      show WindowedLandauTheory.UG.glEquiv g x ∈ Λ
      rw [glEquiv_apply']
      exact (hg x).mp hx
    · intro hy
      refine ⟨(WindowedLandauTheory.UG.glEquiv g).symm y, ?_, ?_⟩
      · rw [hg, ← glEquiv_apply']
        simpa using hy
      · show WindowedLandauTheory.UG.glEquiv g ((WindowedLandauTheory.UG.glEquiv g).symm y) = y
        simp
  · intro hg x
    constructor
    · intro hx
      rw [← hg, Submodule.mem_map]
      exact ⟨x, hx, glEquiv_apply' g x⟩
    · intro hx
      rw [← hg, Submodule.mem_map] at hx
      obtain ⟨z, hz, hzx⟩ := hx
      have hzx' : WindowedLandauTheory.UG.glEquiv g z = (g : Matrix n n K) *ᵥ x := hzx
      have hzx'' : WindowedLandauTheory.UG.glEquiv g z = WindowedLandauTheory.UG.glEquiv g x := by
        rw [hzx', glEquiv_apply']
      rw [← (WindowedLandauTheory.UG.glEquiv g).injective hzx'']
      exact hz

end WindowedLandauTheory.UG.P
