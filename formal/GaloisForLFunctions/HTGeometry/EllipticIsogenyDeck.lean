import GaloisForLFunctions.HTGeometry.EllipticPlaneSubfield

/-!
# The isogeny deck identity for elliptic functions

Scaling the variable by a nonzero factor `m` is the pullback along the isogeny `z ↦ m z` of the
complex torus.  On the field of meromorphic functions of the plane it is a field automorphism, and
it identifies the image of the elliptic functions of a lattice with the functions fixed by every
translation of the preimage lattice:

`planeScale m '' (ellipticSubfield L) = {x | ∀ t, m * t ∈ L.lattice → planeTranslate t x = x}`.

This is the depthwise deck identity of an isogeny protocol, proved with no degree count and no
addition theorem: the deck group of `z ↦ m z` acting on the `L`-elliptic functions is exactly the
group of `m`-division points of the lattice.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Scaling the variable preserves the codiscrete filter. -/
theorem tendsto_mul_const_planeCodiscrete {m : ℂ} (hm : m ≠ 0) :
    Tendsto (fun z : ℂ => m * z) planeCodiscrete planeCodiscrete := by
  refine Filter.tendsto_def.mpr fun S hS => ?_
  refine mem_planeCodiscrete.mpr fun x => ?_
  have hscale : Tendsto (fun w : ℂ => m * w) (𝓝[≠] x) (𝓝[≠] (m * x)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ((by fun_prop : Continuous fun w : ℂ => m * w).tendsto x).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcon
      exact hw (mul_left_cancel₀ hm hcon)
  exact hscale ((mem_planeCodiscrete.mp hS) (m * x))

/-- Scaling of germs along the codiscrete filter. -/
noncomputable def planeGermScale (m : ℂ) (hm : m ≠ 0) (x : Germ planeCodiscrete ℂ) :
    Germ planeCodiscrete ℂ :=
  x.compTendsto (fun z : ℂ => m * z) (tendsto_mul_const_planeCodiscrete hm)

@[simp] theorem planeGermScale_coe (m : ℂ) (hm : m ≠ 0) (f : ℂ → ℂ) :
    planeGermScale m hm (f : Germ planeCodiscrete ℂ)
      = ((fun z : ℂ => f (m * z) : ℂ → ℂ) : Germ planeCodiscrete ℂ) := rfl

theorem planeGermScale_mem {m : ℂ} (hm : m ≠ 0) {g : Germ planeCodiscrete ℂ}
    (hg : g ∈ meromorphicPlaneSubring) : planeGermScale m hm g ∈ meromorphicPlaneSubring := by
  obtain ⟨f, hf, rfl⟩ := hg
  refine ⟨fun z => f (m * z), fun z => ?_, rfl⟩
  exact MeromorphicAt.comp_analyticAt (f := f) (g := fun w : ℂ => m * w) (hf (m * z)) (by fun_prop)

/-- Scaling of the variable on the meromorphic plane field: the pullback along `z ↦ m z`. -/
noncomputable def planeScale (m : ℂ) (hm : m ≠ 0) (x : MeromorphicPlane) : MeromorphicPlane :=
  show MeromorphicPlane from
    ⟨planeGermScale m hm x.germ,
      planeGermScale_mem hm (show (meromorphicPlaneSubring : Type) from x).2⟩

@[simp] theorem germ_planeScale (m : ℂ) (hm : m ≠ 0) (x : MeromorphicPlane) :
    (planeScale m hm x).germ = planeGermScale m hm x.germ := rfl

theorem planeScale_ofMeromorphic (m : ℂ) (hm : m ≠ 0) (f : ℂ → ℂ) (hf : ∀ z, MeromorphicAt f z) :
    planeScale m hm (ofMeromorphic f hf)
      = ofMeromorphic (fun z => f (m * z)) (fun z =>
          MeromorphicAt.comp_analyticAt (f := f) (g := fun w : ℂ => m * w)
            (hf (m * z)) (by fun_prop)) := by
  refine MeromorphicPlane.germ_injective ?_
  rw [germ_planeScale, germ_ofMeromorphic, germ_ofMeromorphic, planeGermScale_coe]

theorem planeScale_one (x : MeromorphicPlane) : planeScale 1 one_ne_zero x = x := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  rw [planeScale_ofMeromorphic]
  refine MeromorphicPlane.germ_injective ?_
  rw [germ_ofMeromorphic, germ_ofMeromorphic]
  simp

theorem planeScale_planeScale {m n : ℂ} (hm : m ≠ 0) (hn : n ≠ 0) (x : MeromorphicPlane) :
    planeScale m hm (planeScale n hn x) = planeScale (n * m) (mul_ne_zero hn hm) x := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  rw [planeScale_ofMeromorphic, planeScale_ofMeromorphic, planeScale_ofMeromorphic]
  refine MeromorphicPlane.germ_injective ?_
  rw [germ_ofMeromorphic, germ_ofMeromorphic]
  refine Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => ?_)
  show f (n * (m * z)) = f (n * m * z)
  rw [mul_assoc]

theorem planeScale_map_add (m : ℂ) (hm : m ≠ 0) (x y : MeromorphicPlane) :
    planeScale m hm (x + y) = planeScale m hm x + planeScale m hm y := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  obtain ⟨g, hg, rfl⟩ := y.exists_rep
  rw [ofMeromorphic_add, planeScale_ofMeromorphic, planeScale_ofMeromorphic,
    planeScale_ofMeromorphic, ofMeromorphic_add]
  refine MeromorphicPlane.germ_injective ?_
  rw [germ_ofMeromorphic, germ_ofMeromorphic]
  exact Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => rfl)

theorem planeScale_map_mul (m : ℂ) (hm : m ≠ 0) (x y : MeromorphicPlane) :
    planeScale m hm (x * y) = planeScale m hm x * planeScale m hm y := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  obtain ⟨g, hg, rfl⟩ := y.exists_rep
  rw [ofMeromorphic_mul, planeScale_ofMeromorphic, planeScale_ofMeromorphic,
    planeScale_ofMeromorphic, ofMeromorphic_mul]
  refine MeromorphicPlane.germ_injective ?_
  rw [germ_ofMeromorphic, germ_ofMeromorphic]
  exact Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => rfl)

/-- Scaling of the variable commutes with translation, up to scaling the translation vector. -/
theorem planeScale_planeTranslate (m : ℂ) (hm : m ≠ 0) (t : ℂ) (x : MeromorphicPlane) :
    planeScale m hm (planeTranslate t x) = planeTranslate (t / m) (planeScale m hm x) := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  rw [planeTranslate_ofMeromorphic, planeScale_ofMeromorphic, planeScale_ofMeromorphic,
    planeTranslate_ofMeromorphic]
  refine MeromorphicPlane.germ_injective ?_
  rw [germ_ofMeromorphic, germ_ofMeromorphic]
  refine Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => ?_)
  show f (m * z + t) = f (m * (z + t / m))
  congr 1
  field_simp

/-- Scaling by equal factors agrees. -/
theorem planeScale_congr {m n : ℂ} (hm : m ≠ 0) (hn : n ≠ 0) (h : m = n) (x : MeromorphicPlane) :
    planeScale m hm x = planeScale n hn x := by
  subst h
  rfl

/-- **The isogeny deck identity.**  A meromorphic function is the pullback along `z ↦ m z` of an
`L`-elliptic function exactly when it is invariant under every translation whose `m`-fold multiple
is a period. -/
theorem exists_mem_ellipticSubfield_planeScale_iff (L : PeriodPair) {m : ℂ} (hm : m ≠ 0)
    (x : MeromorphicPlane) :
    (∃ y ∈ ellipticSubfield L, planeScale m hm y = x)
      ↔ ∀ t : ℂ, m * t ∈ L.lattice → planeTranslate t x = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩ t ht
    have hmt := hy (m * t) ht
    have hscale := planeScale_planeTranslate m hm (m * t) y
    rw [hmt] at hscale
    have harg : m * t / m = t := by field_simp
    rw [harg] at hscale
    exact hscale.symm
  · intro hx
    have hminv : m⁻¹ ≠ 0 := inv_ne_zero hm
    refine ⟨planeScale m⁻¹ hminv x, ?_, ?_⟩
    · intro p hp
      have hmp : m * (p / m) = p := by field_simp
      have hfix : planeTranslate (p / m) x = x := hx (p / m) (by rw [hmp]; exact hp)
      have hscale := planeScale_planeTranslate m⁻¹ hminv (p / m) x
      rw [hfix] at hscale
      have harg : p / m / m⁻¹ = p := by field_simp
      rw [harg] at hscale
      exact hscale.symm
    · rw [planeScale_planeScale hm hminv x,
        planeScale_congr (mul_ne_zero hminv hm) one_ne_zero (inv_mul_cancel₀ hm) x,
        planeScale_one]

end GaloisForLFunctions.HTGeometry
