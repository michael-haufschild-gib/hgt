import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneClasses
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Algebra.Module.Submodule.Equiv

/-! Direct sums and character twists of Weil–Deligne representations descend
to isomorphism classes. Unramified twists preserve the tame inertia action. -/

noncomputable section

open NumberField IsDedekindDomain Module Polynomial
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.TameKummer

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem isSmooth_unrChar (h : IsPlaceOver A w) (c : ℂˣ) : IsSmooth (unrChar h c) :=
  .of_trivial fun σ => by simp

namespace WDRep

variable {V V' V'' V''' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup V''] [Module ℂ V''] [FiniteDimensional ℂ V'']
  [AddCommGroup V'''] [Module ℂ V'''] [FiniteDimensional ℂ V''']

private theorem isSemisimple_of_iSup_eigenspace {f : End ℂ V}
    (hf : ⨆ α, f.eigenspace α = ⊤) : f.IsSemisimple := by
  classical
  have hfin : Set.Finite {α : ℂ | f.HasEigenvalue α} := Module.End.finite_hasEigenvalue f
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := ∏ α ∈ hfin.toFinset, (X - C α))
    (separable_prod_X_sub_C_iff'.mpr fun _ _ _ _ h => h).squarefree ?_
  rw [← LinearMap.ker_eq_top, eq_top_iff, ← hf]
  refine iSup_le fun α v hv => ?_
  by_cases hα : f.HasEigenvalue α
  · rw [LinearMap.mem_ker, ← Finset.prod_erase_mul _ _ (hfin.mem_toFinset.mpr hα), map_mul,
      End.mul_apply]
    have : aeval f (X - C α) v = 0 := by simp [End.mem_eigenspace_iff.mp hv]
    rw [this, map_zero]
  · rw [End.hasEigenvalue_iff, not_not] at hα
    rw [hα, Submodule.mem_bot] at hv
    rw [hv]
    exact zero_mem _

private theorem isSemisimple_prodMap {f : End ℂ V} {g : End ℂ V'}
    (hf : f.IsSemisimple) (hg : g.IsSemisimple) :
    End.IsSemisimple (f.prodMap g : End ℂ (V × V')) := by
  refine isSemisimple_of_iSup_eigenspace ?_
  rw [eq_top_iff, ← Submodule.prod_top, ← hf.iSup_eigenspace_eq_top, ← hg.iSup_eigenspace_eq_top,
    LinearMap.prod_eq_sup_map, Submodule.map_iSup, Submodule.map_iSup]
  refine sup_le (iSup_mono fun α => ?_) (iSup_mono fun α => ?_)
  · rintro _ ⟨v, hv, rfl⟩
    simpa [End.mem_eigenspace_iff] using hv
  · rintro _ ⟨v, hv, rfl⟩
    simpa [End.mem_eigenspace_iff] using hv

/-- Direct sum with monodromy acting componentwise. -/
def sum (a : WDRep h V) (b : WDRep h V') : WDRep h (V × V') where
  ρ := a.ρ.prod b.ρ
  N := a.N.prodMap b.N
  smooth := a.smooth.of_le₂ b.smooth fun σ h₁ h₂ => by
    change (a.ρ σ).prodMap (b.ρ σ) = 1
    rw [h₁, h₂]
    exact LinearMap.prodMap_one
  semisimple σ := isSemisimple_prodMap (a.semisimple σ) (b.semisimple σ)
  nilpotent := by
    have hp (n : ℕ) : (a.N.prodMap b.N : End ℂ (V × V')) ^ n = (a.N ^ n).prodMap (b.N ^ n) :=
      (map_pow (LinearMap.prodMapRingHom ℂ V V') (a.N, b.N) n).symm
    obtain ⟨m, hm⟩ := a.nilpotent
    obtain ⟨n, hn⟩ := b.nilpotent
    exact ⟨m + n, by rw [hp, pow_add, hm, zero_mul, pow_add, hn, mul_zero, LinearMap.prodMap_zero]⟩
  comm σ := LinearMap.ext fun v => Prod.ext (a.comm_apply σ v.1) (b.comm_apply σ v.2)

omit [IsAlgClosure E Ω] in
theorem Iso.sum {a : WDRep h V} {a' : WDRep h V'} {b : WDRep h V''} {b' : WDRep h V'''}
    (ha : a.Iso a') (hb : b.Iso b') : (a.sum b).Iso (a'.sum b') := by
  obtain ⟨e, hρ, hN⟩ := ha
  obtain ⟨e', hρ', hN'⟩ := hb
  exact ⟨e.prodCongr e', fun σ v => Prod.ext (hρ σ v.1) (hρ' σ v.2),
    fun v => Prod.ext (hN v.1) (hN' v.2)⟩

/-- Multiplication of the Weil operators by a smooth character. -/
def twist (a : WDRep h V) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) : WDRep h V where
  ρ := { toFun := fun σ => (χ σ : ℂ) • a.ρ σ
         map_one' := by simp
         map_mul' := fun σ τ => by simp [smul_smul, mul_comm] }
  N := a.N
  smooth := a.smooth.of_le₂ hχ fun σ h₁ h₂ => by simp [h₁, h₂]
  semisimple σ := End.IsSemisimple_smul _ (a.semisimple σ)
  nilpotent := a.nilpotent
  comm σ := by
    change ((χ σ : ℂ) • a.ρ σ) * a.N = _ • (a.N * ((χ σ : ℂ) • a.ρ σ))
    rw [smul_mul_assoc, a.comm, mul_smul_comm, smul_comm]

omit [IsAlgClosure E Ω] in
theorem Iso.twist {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) (χ : Weil h →* ℂˣ)
    (hχ : IsSmooth χ) : (a.twist χ hχ).Iso (b.twist χ hχ) := by
  obtain ⟨e, hρ, hN⟩ := hab
  exact ⟨e, fun σ v => by
    change e ((χ σ : ℂ) • a.ρ σ v) = (χ σ : ℂ) • b.ρ σ (e v)
    rw [map_smul, hρ], hN⟩

theorem charpoly_twist_on_inertia (a : WDRep h V) (c : ℂˣ) (τ : Ine (F := E) A) :
    ((a.twist (unrChar h c) (isSmooth_unrChar h c)).ρ (ineIncl h τ)).charpoly =
      (a.ρ (ineIncl h τ)).charpoly := by
  change (((unrChar h c) (ineIncl h τ) : ℂ) • a.ρ (ineIncl h τ)).charpoly = _
  simp

omit [IsAlgClosure E Ω] in
theorem charpoly_sum (a : WDRep h V) (b : WDRep h V') (σ : Weil h) :
    ((a.sum b).ρ σ).charpoly = (a.ρ σ).charpoly * (b.ρ σ).charpoly :=
  LinearMap.charpoly_prodMap _ _

/-- Wild inertia fixes the direct sum exactly when it fixes both components. -/
theorem tamePart_sum_iso (a : WDRep h V) (b : WDRep h V') :
    (a.sum b).tamePart.Iso (a.tamePart.sum b.tamePart) := by
  have hmem (v : V × V') : v ∈ (a.sum b).tameSpace ↔
      v.1 ∈ a.tameSpace ∧ v.2 ∈ b.tameSpace := by
    rw [(a.sum b).mem_tameSpace, a.mem_tameSpace, b.mem_tameSpace]
    refine ⟨fun hv => ⟨fun σ hs => ?_, fun σ hs => ?_⟩, fun hv σ hs => ?_⟩
    · exact congrArg Prod.fst (hv σ hs)
    · exact congrArg Prod.snd (hv σ hs)
    · exact Prod.ext (hv.1 σ hs) (hv.2 σ hs)
  let e : (a.sum b).tameSpace ≃ₗ[ℂ] a.tameSpace × b.tameSpace :=
    { toFun := fun v => ⟨⟨v.1.1, ((hmem v).mp v.2).1⟩, ⟨v.1.2, ((hmem v).mp v.2).2⟩⟩
      invFun := fun u => ⟨(u.1.1, u.2.1), (hmem _).mpr ⟨u.1.2, u.2.2⟩⟩
      left_inv := fun v => Subtype.ext (Prod.eta _)
      right_inv := fun v => Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
      map_add' := fun _ _ => Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
      map_smul' := fun _ _ => Prod.ext (Subtype.ext rfl) (Subtype.ext rfl) }
  exact ⟨e, fun _ _ => Prod.ext (Subtype.ext rfl) (Subtype.ext rfl),
    fun _ => Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)⟩

/-- Taking wild inertia invariants commutes with an unramified twist. -/
theorem tamePart_unramified_twist_iso (a : WDRep h V) (c : ℂˣ) :
    (a.twist (unrChar h c) (isSmooth_unrChar h c)).tamePart.Iso
      (a.tamePart.twist (unrChar h c) (isSmooth_unrChar h c)) := by
  let b := a.twist (unrChar h c) (isSmooth_unrChar h c)
  have hρ (σ : Weil h) (hσ : (σ : G E Ω) ∈ wildInertia A) : b.ρ σ = a.ρ σ := by
    change ((unrChar h c σ : ℂ) • a.ρ σ) = _
    simp [deg_eq_zero_iff.mpr (wildInertia_le_inertia A hσ)]
  have he : b.tameSpace = a.tameSpace := by
    ext v
    rw [b.mem_tameSpace, a.mem_tameSpace]
    exact ⟨fun hv σ hs => hρ σ hs ▸ hv σ hs, fun hv σ hs => (hρ σ hs).symm ▸ hv σ hs⟩
  exact ⟨LinearEquiv.ofEq _ _ he, fun _ _ => Subtype.ext rfl, fun _ => Subtype.ext rfl⟩

private def diagEnd {ι : Type} (c : ι → ℂ) : End ℂ (ι → ℂ) where
  toFun v i := c i * v i
  map_add' v v' := by ext; simp [mul_add]
  map_smul' a v := by ext; simp [mul_left_comm]

@[simp] private theorem diagEnd_apply {ι : Type} (c v : ι → ℂ) (i : ι) :
    diagEnd c v i = c i * v i := rfl

private theorem isSemisimple_diagEnd {ι : Type} [Fintype ι] (c : ι → ℂ) : (diagEnd c).IsSemisimple := by
  classical
  refine isSemisimple_of_iSup_eigenspace (eq_top_iff.mpr fun v _ => ?_)
  rw [← Finset.univ_sum_single v]
  refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem (c i) ?_
  rw [End.mem_eigenspace_iff]
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

private theorem charpoly_diagEnd {ι : Type} [Fintype ι] (c : ι → ℂ) :
    (diagEnd c).charpoly = ∏ i, (X - C (c i)) := by
  classical
  have e : diagEnd c = Matrix.toLin' (Matrix.diagonal c) := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [Matrix.mulVec_diagonal]
  rw [e, Matrix.charpoly_toLin', Matrix.charpoly_diagonal]

/-- The direct sum of finitely many rank-one Weil characters, with zero monodromy. -/
def ofChars {ι : Type} [Fintype ι] (χ : ι → Weil h →* ℂˣ) (hχ : ∀ i, IsSmooth (χ i)) :
    WDRep h (ι → ℂ) where
  ρ := { toFun := fun σ => diagEnd fun i => (χ i σ : ℂ)
         map_one' := by ext; simp
         map_mul' := fun σ τ => LinearMap.ext fun v => funext fun i => by simp [mul_assoc] }
  N := 0
  smooth := .of_open (isOpen_iInter_of_finite hχ) (by simp) fun σ hσ =>
    LinearMap.ext fun v => funext fun i => by
      have he : χ i (ineIncl h σ) = 1 := Set.mem_iInter.mp hσ i
      simp [he]
  semisimple σ := isSemisimple_diagEnd _
  nilpotent := IsNilpotent.zero
  comm σ := by simp

omit [IsAlgClosure E Ω] in
theorem charpoly_ofChars {ι : Type} [Fintype ι] (χ : ι → Weil h →* ℂˣ)
    (hχ : ∀ i, IsSmooth (χ i)) (σ : Weil h) :
    ((ofChars χ hχ).ρ σ).charpoly = ∏ i, (X - C (χ i σ : ℂ)) :=
  charpoly_diagEnd _

def Unr (a : WDRep h V) : Prop := a.N = 0 ∧ ∀ σ : Ine (F := E) A, a.ρ (ineIncl h σ) = 1

omit [IsAlgClosure E Ω] in
theorem Iso.unr {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) (ha : a.Unr) : b.Unr :=
  ⟨hab.monodromy_eq_zero ha.1, fun σ => hab.ρ_eq_one (ha.2 σ)⟩

/-- A diagonal unramified parameter with prescribed Frobenius eigenvalues. -/
def diag {ι : Type} [Fintype ι] (c : ι → ℂˣ) : WDRep h (ι → ℂ) :=
  ofChars (fun i => unrChar h (c i)) fun _ => isSmooth_unrChar h _

@[simp] theorem diag_ρ_apply {ι : Type} [Fintype ι] (c : ι → ℂˣ) (σ : Weil h) (v : ι → ℂ) (i : ι) :
    (diag c).ρ σ v i = (c i : ℂ) ^ deg σ * v i := by
  change (unrChar h (c i) σ : ℂ) * v i = _
  simp

@[simp] theorem diag_N {ι : Type} [Fintype ι] (c : ι → ℂˣ) :
    (diag (h := h) c).N = 0 := rfl

theorem unr_diag {ι : Type} [Fintype ι] (c : ι → ℂˣ) : (diag (h := h) c).Unr :=
  ⟨rfl, fun σ => LinearMap.ext fun v => funext fun i => by
    change ((unrChar h (c i) (ineIncl h σ) : ℂ) * v i) = v i
    simp⟩

theorem charpoly_diag_frob {ι : Type} [Fintype ι] (c : ι → ℂˣ) :
    ((diag c).ρ (frob h)).charpoly = ∏ i, (X - C (c i : ℂ)) := by
  rw [diag, charpoly_ofChars]
  simp

end WDRep

namespace WD

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

def lpSum (x y : WD h) : WD h :=
  Quotient.lift₂ (s₁ := isoSetoid h) (s₂ := isoSetoid h) (fun a b => mk (a.2.sum b.2))
    (fun _ _ _ _ ha hb => sound (WDRep.Iso.sum ha hb)) x y

@[simp] theorem lpSum_mk (a : WDRep h V) (b : WDRep h V') :
    lpSum (mk a) (mk b) = mk (a.sum b) :=
  sound ((iso_std a).sum (iso_std b)).symm

def lpTwist (x : WD h) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) : WD h :=
  Quotient.lift (s := isoSetoid h) (fun a => mk (a.2.twist χ hχ))
    (fun _ _ hab => sound (WDRep.Iso.twist hab χ hχ)) x

@[simp] theorem lpTwist_mk (a : WDRep h V) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) :
    lpTwist (mk a) χ hχ = mk (a.twist χ hχ) :=
  sound ((iso_std a).twist χ hχ).symm

theorem lpDim_sum (x y : WD h) : (lpSum x y).lpDim = x.lpDim + y.lpDim := by
  refine WD.ind (fun n a => ?_) x
  refine WD.ind (fun m b => ?_) y
  simp only [lpSum_mk, lpDim_mk, Module.finrank_prod]

theorem lpDim_twist (x : WD h) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) :
    (lpTwist x χ hχ).lpDim = x.lpDim := by
  refine WD.ind (fun n a => ?_) x
  simp only [lpTwist_mk, lpDim_mk]

theorem charpoly_sum (x y : WD h) (σ : Weil h) :
    (lpSum x y).charpoly σ = x.charpoly σ * y.charpoly σ := by
  refine WD.ind (fun n a => ?_) x
  refine WD.ind (fun m b => ?_) y
  simp only [lpSum_mk, charpoly_mk, WDRep.charpoly_sum]

theorem charpoly_unramified_twist_on_inertia (x : WD h) (c : ℂˣ) (τ : Ine (F := E) A) :
    (lpTwist x (unrChar h c) (isSmooth_unrChar h c)).charpoly (ineIncl h τ) =
      x.charpoly (ineIncl h τ) := by
  refine WD.ind (fun n a => ?_) x
  simp only [lpTwist_mk, charpoly_mk, WDRep.charpoly_twist_on_inertia]

theorem lpTame_sum (x y : WD h) : (lpSum x y).lpTame = lpSum x.lpTame y.lpTame := by
  refine WD.ind (fun n a => ?_) x
  refine WD.ind (fun m b => ?_) y
  simp only [lpSum_mk, lpTame_mk]
  exact sound (a.tamePart_sum_iso b)

theorem lpTame_unramified_twist (x : WD h) (c : ℂˣ) :
    (lpTwist x (unrChar h c) (isSmooth_unrChar h c)).lpTame =
      lpTwist x.lpTame (unrChar h c) (isSmooth_unrChar h c) := by
  refine WD.ind (fun n a => ?_) x
  simp only [lpTwist_mk, lpTame_mk]
  exact sound (a.tamePart_unramified_twist_iso c)

def unr (x : WD h) : Prop :=
  Quotient.lift (s := isoSetoid h) (fun a => a.2.Unr)
    (fun _ _ hab => propext ⟨WDRep.Iso.unr hab, WDRep.Iso.unr (WDRep.Iso.symm hab)⟩) x

@[simp] theorem unr_mk (a : WDRep h V) : unr (mk a) ↔ a.Unr :=
  ⟨(iso_std a).symm.unr, (iso_std a).unr⟩

/-- Realize a finite ordered family of nonzero Frobenius eigenvalues. -/
def lpUnr {ι : Type} [Fintype ι] (a : ι → ℂˣ) : WD h :=
  mk (WDRep.diag (h := h) a)

theorem unr_lpUnr {ι : Type} [Fintype ι] (a : ι → ℂˣ) : (lpUnr (h := h) a).unr :=
  (unr_mk _).mpr (WDRep.unr_diag a)

theorem lpDim_lpUnr {ι : Type} [Fintype ι] (a : ι → ℂˣ) :
    (lpUnr (h := h) a).lpDim = Fintype.card ι := by
  rw [lpUnr, lpDim_mk, Module.finrank_fintype_fun_eq_card]

theorem charpoly_lpUnr_frob {ι : Type} [Fintype ι] (a : ι → ℂˣ) :
    (lpUnr a).charpoly (frob h) = ∏ i, (X - C (a i : ℂ)) := by
  rw [lpUnr, charpoly_mk, WDRep.charpoly_diag_frob]

end WD
end GlobalTheory.WeilDeligne
