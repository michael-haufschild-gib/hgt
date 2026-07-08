import GaloisForLFunctions.RHTower.SeamPolarizationWeld
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# The three faces of "Lorentzian" for a polarized seam form

A metric is *Lorentzian* when it has (1) exactly one time direction, (2) a nondegenerate metric, and
(3) a light cone.  For the seam supermetric `Q` — a symmetric form carrying a compatible complex
structure `J` (`J² = -1`, `Q(J·,J·) = Q`) — the single mechanism "`J` pairs every direction with its
partner" answers all three, and each answer separates the seam from Lorentzian geometry:

* **One time direction — false.**  `sigNeg` (the negative index, the number of time directions) is
  **even**, even when `Q` is degenerate (`polarized_sigNeg_even`).  Applied to `-Q` it makes the
  positive index even too.  A time direction never stands alone: it is welded to its `J`-partner, so
  the count is `0, 2, 4, …`, never the Lorentzian `1`.

* **Degeneracy is even.**  The radical `Q.orthogonal ⊤` is `J`-invariant, hence even-dimensional
  (`radical_finrank_even`).  If the metric degenerates, it degenerates in `J`-pairs — the null
  directions of the radical come welded too.

* **The light cone is fat.**  A single nonzero null vector `x` drags its whole `J`-plane
  `span{x, J x}` into the null cone as a **2-dimensional totally isotropic subspace**
  (`null_forces_isotropic_plane`).  A Lorentzian cone has Witt index `1` — its maximal totally
  isotropic subspace is a line.  The seam's cone contains planes, so it is not Lorentzian read from
  the null side either.

Together: the full inertia triple `(sigPos, sigNeg, dim radical)` of the seam supermetric is
`(2a, 2b, 2c)` — neutral, never Lorentzian `(n−1, 1, 0)`.  This is the functional equation's
conjugate-pairing of zeros seen as a rigidity of `J`, not a flow.
-/

noncomputable section

open GaloisForLFunctions GaloisForLFunctions.RHTower

namespace RHTower

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ### Characteristic 1 — time directions come in `J`-pairs (`sigNeg` even) -/

/-- A negative-definite subspace of `Q` is a `PosDef` subspace of `-Q.toQuadraticMap` — the data the
negative index of inertia `sigNeg` maximizes over. -/
theorem negdef_restrict_posdef {Q : LinearMap.BilinForm ℝ V} {W : Submodule ℝ V}
    (h : ∀ v ∈ W, v ≠ 0 → Q v v < 0) :
    (QuadraticMap.restrict (-(LinearMap.BilinMap.toQuadraticMap Q)) W).PosDef := by
  rintro ⟨v, hv⟩ hne
  have hv0 : v ≠ 0 := fun hh => hne (Subtype.ext hh)
  have heq : (QuadraticMap.restrict (-(LinearMap.BilinMap.toQuadraticMap Q)) W) ⟨v, hv⟩
      = -(Q v v) := by
    simp [QuadraticMap.restrict_apply, LinearMap.BilinMap.toQuadraticMap_apply]
  rw [heq]; linarith [h v hv hv0]

/-- The subspace witnessing `sigNeg` is negative-definite of dimension `sigNeg`. -/
theorem sigNeg_negdef_witness {Q : LinearMap.BilinForm ℝ V} [FiniteDimensional ℝ V] :
    ∃ U : Submodule ℝ V, Module.finrank ℝ U = sigNeg (LinearMap.BilinMap.toQuadraticMap Q) ∧
      ∀ y ∈ U, y ≠ 0 → Q y y < 0 := by
  obtain ⟨U, hUdim, hUpd⟩ :=
    exists_finrank_eq_sigNeg_and_negDef (LinearMap.BilinMap.toQuadraticMap Q)
  refine ⟨U, hUdim, fun y hy hy0 => ?_⟩
  have hpos := hUpd ⟨y, hy⟩ (fun hh => hy0 (Subtype.ext_iff.mp hh))
  have heq : (QuadraticMap.restrict (-(LinearMap.BilinMap.toQuadraticMap Q)) U) ⟨y, hy⟩
      = -(Q y y) := by
    simp [QuadraticMap.restrict_apply, LinearMap.BilinMap.toQuadraticMap_apply]
  rw [heq] at hpos; linarith

/-- **A `J`-invariant negative-definite subspace smaller than `sigNeg` extends by a whole `J`-plane.**
A maximal negative-definite subspace `U` meets the (`J`-invariant) `Q`-orthogonal complement of `W` in
a nonzero `v` with `Q(v,v) < 0`; its `J`-plane `span{v, J v}` lies in `Wᗮ`, is negative-definite and
`2`-dimensional, and adjoins `W` orthogonally.  The dimension count uses
`finrank_add_finrank_orthogonal'`, so **no nondegeneracy of `Q` is assumed.** -/
theorem extend_Jinvariant_negdef {Q : LinearMap.BilinForm ℝ V} [FiniteDimensional ℝ V]
    (P : PolarizedOmegaComplexStructure V Q) (hQ : Q.IsSymm) {W : Submodule ℝ V}
    (hWJ : ∀ w ∈ W, P.complex.J w ∈ W) (hWneg : ∀ y ∈ W, y ≠ 0 → Q y y < 0)
    (hlt : Module.finrank ℝ W < sigNeg (LinearMap.BilinMap.toQuadraticMap Q)) :
    ∃ W' : Submodule ℝ V, (∀ w ∈ W', P.complex.J w ∈ W') ∧
      (∀ y ∈ W', y ≠ 0 → Q y y < 0) ∧ Module.finrank ℝ W' = Module.finrank ℝ W + 2 := by
  obtain ⟨U, hUdim, hUneg⟩ := sigNeg_negdef_witness (Q := Q)
  have heqOrtho := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := Q) W
  have hbound : Module.finrank ℝ V ≤ Module.finrank ℝ W + Module.finrank ℝ (Q.orthogonal W) := by
    omega
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq U (Q.orthogonal W)
  have hle : Module.finrank ℝ ((U ⊔ Q.orthogonal W : Submodule ℝ V)) ≤ Module.finrank ℝ V :=
    Submodule.finrank_le _
  have hpos : 0 < Module.finrank ℝ ((U ⊓ Q.orthogonal W : Submodule ℝ V)) := by omega
  have hne : (U ⊓ Q.orthogonal W : Submodule ℝ V) ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hpos; exact lt_irrefl 0 hpos
  obtain ⟨v, hvmem, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Submodule.mem_inf] at hvmem
  obtain ⟨hvU, hvOW⟩ := hvmem
  have hvneg : Q v v < 0 := hUneg v hvU hv0
  set plane := Submodule.span ℝ ({v, P.complex.J v} : Set V) with hplane
  have hplaneJ : ∀ w ∈ plane, P.complex.J w ∈ plane := polarized_plane_Jinvariant P.complex v
  have hplaneNeg : ∀ y ∈ plane, y ≠ 0 → Q y y < 0 := polarized_negDef_plane P hQ hvneg
  have hplaneDim : Module.finrank ℝ plane = 2 := polarized_negDef_plane_finrank P hv0
  have hJvOW : P.complex.J v ∈ Q.orthogonal W := orthogonal_Jinvariant P hWJ v hvOW
  have hplane_le : plane ≤ Q.orthogonal W := by
    rw [hplane, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hvOW, hJvOW⟩
  have hcross : ∀ a ∈ W, ∀ b ∈ plane, Q a b = 0 := by
    intro a ha b hb
    have hbOW := hplane_le hb
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hbOW
    have := hbOW a ha
    rwa [LinearMap.BilinForm.isOrtho_def] at this
  refine ⟨W ⊔ plane, sup_Jinvariant P.complex hWJ hplaneJ,
    negDef_sup hQ hWneg hplaneNeg hcross, ?_⟩
  have hWplane_bot : (W ⊓ plane : Submodule ℝ V) = ⊥ := by
    rw [eq_bot_iff]; intro w hw
    rw [Submodule.mem_inf] at hw
    obtain ⟨hwW, hwP⟩ := hw
    by_contra hwne
    rw [Submodule.mem_bot] at hwne
    have hwneg : Q w w < 0 := hplaneNeg w hwP hwne
    have hwzero : Q w w = 0 := hcross w hwW w hwP
    rw [hwzero] at hwneg; exact lt_irrefl 0 hwneg
  have hsup2 := Submodule.finrank_sup_add_finrank_inf_eq W plane
  rw [hWplane_bot, finrank_bot, hplaneDim] at hsup2
  omega

/-- A `J`-invariant negative-definite subspace of every even dimension up to `sigNeg` exists. -/
theorem build_even_negdef {Q : LinearMap.BilinForm ℝ V} [FiniteDimensional ℝ V]
    (P : PolarizedOmegaComplexStructure V Q) (hQ : Q.IsSymm) :
    ∀ m : ℕ, 2 * m ≤ sigNeg (LinearMap.BilinMap.toQuadraticMap Q) →
      ∃ W : Submodule ℝ V, (∀ w ∈ W, P.complex.J w ∈ W) ∧
        (∀ y ∈ W, y ≠ 0 → Q y y < 0) ∧ Module.finrank ℝ W = 2 * m := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨⊥, fun w hw => ?_, fun y hy hy0 => ?_, by simp⟩
    · rw [Submodule.mem_bot] at hw ⊢; rw [hw, map_zero]
    · rw [Submodule.mem_bot] at hy; exact absurd hy hy0
  | succ k ih =>
    intro hk
    obtain ⟨W, hWJ, hWneg, hWdim⟩ := ih (by omega)
    have hlt : Module.finrank ℝ W < sigNeg (LinearMap.BilinMap.toQuadraticMap Q) := by
      rw [hWdim]; omega
    obtain ⟨W', hW'J, hW'neg, hW'dim⟩ := extend_Jinvariant_negdef P hQ hWJ hWneg hlt
    exact ⟨W', hW'J, hW'neg, by rw [hW'dim, hWdim]; ring⟩

/-- **The negative index of a polarized symmetric form is even — even when `Q` is degenerate.**  Were
`sigNeg` odd, `build_even_negdef` would give a `J`-invariant negative-definite subspace of dimension
`sigNeg − 1`, which `extend_Jinvariant_negdef` grows to `sigNeg + 1`, exceeding the index.  So time
directions never stand alone: the count is `0, 2, 4, …`, never the Lorentzian `1`.  This drops the
nondegeneracy hypothesis of `polarized_negIndex_even` and reads the index through mathlib's `sigNeg`. -/
theorem polarized_sigNeg_even {Q : LinearMap.BilinForm ℝ V} [FiniteDimensional ℝ V]
    (P : PolarizedOmegaComplexStructure V Q) (hQ : Q.IsSymm) :
    Even (sigNeg (LinearMap.BilinMap.toQuadraticMap Q)) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨W, hWJ, hWneg, hWdim⟩ := build_even_negdef P hQ k (by omega)
  have hlt : Module.finrank ℝ W < sigNeg (LinearMap.BilinMap.toQuadraticMap Q) := by
    rw [hWdim]; omega
  obtain ⟨W', _, hW'neg, hW'dim⟩ := extend_Jinvariant_negdef P hQ hWJ hWneg hlt
  have hle :=
    le_sigNeg_of_negDef (LinearMap.BilinMap.toQuadraticMap Q) (negdef_restrict_posdef hW'neg)
  rw [hW'dim, hWdim] at hle; omega

/-- The polarization carries over to `-Q`: the same `J` preserves `-Q`. -/
def polarizedNeg {Q : LinearMap.BilinForm ℝ V} (P : PolarizedOmegaComplexStructure V Q) :
    PolarizedOmegaComplexStructure V (-Q) where
  complex := P.complex
  preserves x y := by
    show (-Q) (P.complex.J x) (P.complex.J y) = (-Q) x y
    simp only [LinearMap.neg_apply]
    rw [P.preserves x y]

theorem neg_isSymm {Q : LinearMap.BilinForm ℝ V} (hQ : Q.IsSymm) : (-Q).IsSymm :=
  ⟨fun x y => by simp only [LinearMap.neg_apply]; exact congrArg Neg.neg (hQ.eq x y)⟩

theorem toQuadraticMap_neg (Q : LinearMap.BilinForm ℝ V) :
    LinearMap.BilinMap.toQuadraticMap (-Q) = -(LinearMap.BilinMap.toQuadraticMap Q) := by
  ext x; simp [LinearMap.BilinMap.toQuadraticMap_apply]

/-- **The positive index is even too** (apply `polarized_sigNeg_even` to `-Q`, whose `J`-polarization
is `polarizedNeg`). -/
theorem polarized_sigPos_even {Q : LinearMap.BilinForm ℝ V} [FiniteDimensional ℝ V]
    (P : PolarizedOmegaComplexStructure V Q) (hQ : Q.IsSymm) :
    Even (sigPos (LinearMap.BilinMap.toQuadraticMap Q)) := by
  have h := polarized_sigNeg_even (polarizedNeg P) (neg_isSymm hQ)
  rw [toQuadraticMap_neg] at h
  rwa [sigNeg, neg_neg] at h

/-- **Not Lorentzian.**  The negative index of the seam supermetric is never `1`: a lone time
direction is impossible under a polarization. -/
theorem polarized_not_lorentzian {Q : LinearMap.BilinForm ℝ V} [FiniteDimensional ℝ V]
    (P : PolarizedOmegaComplexStructure V Q) (hQ : Q.IsSymm) :
    sigNeg (LinearMap.BilinMap.toQuadraticMap Q) ≠ 1 := by
  intro h1
  have h := polarized_sigNeg_even P hQ
  rw [h1] at h
  exact (Nat.not_even_iff_odd.mpr ⟨0, rfl⟩) h

/-! ### Characteristic 2 — degeneracy comes in `J`-pairs -/

/-- **The radical of a polarized form is `J`-invariant.**  If `Q v = 0` on all of `V`, then so does
`Q (J v)`, because `Q(J v, ·) = -Q(v, J ·)`.  The radical is `Q.orthogonal ⊤`, and `⊤` is trivially
`J`-invariant, so this is the `orthogonal_Jinvariant` lemma at `U = ⊤`. -/
theorem radical_Jinvariant {Q : LinearMap.BilinForm ℝ V}
    (P : PolarizedOmegaComplexStructure V Q) :
    ∀ v ∈ Q.orthogonal ⊤, P.complex.J v ∈ Q.orthogonal ⊤ :=
  orthogonal_Jinvariant P (fun _ _ => Submodule.mem_top)

/-- **The radical is even-dimensional.**  A `J`-invariant subspace carries a restricted complex
structure, so its dimension is even (`Jinvariant_subspace_finrank_even`).  Hence if the seam metric is
degenerate, its degeneracy occurs only in `J`-conjugate pairs — there is no lone null direction in the
radical. -/
theorem radical_finrank_even [FiniteDimensional ℝ V] {Q : LinearMap.BilinForm ℝ V}
    (P : PolarizedOmegaComplexStructure V Q) :
    Even (Module.finrank ℝ (Q.orthogonal ⊤)) :=
  Jinvariant_subspace_finrank_even P.complex (radical_Jinvariant P)

/-! ### Characteristic 3 — the light cone contains `J`-planes -/

/-- **A null direction fills a totally isotropic `J`-plane.**  If `Q(x,x) = 0` then on
`span{x, J x}` the form vanishes identically: `Q(a·x + b·J x, a·x + b·J x) = (a²+b²)·Q(x,x) = 0`.
So every isotropic vector spans a plane on which `Q` is totally null. -/
theorem null_plane_self_isotropic {Q : LinearMap.BilinForm ℝ V}
    (P : PolarizedOmegaComplexStructure V Q) (hQ : Q.IsSymm) {x : V} (hx : Q x x = 0) :
    ∀ y ∈ Submodule.span ℝ ({x, P.complex.J x} : Set V), Q y y = 0 := by
  intro y hy
  rw [Submodule.mem_span_pair] at hy
  obtain ⟨a, b, rfl⟩ := hy
  rw [P.Q_apply_span_self_of_isSymm hQ, hx, mul_zero]

/-- **The `J`-plane of a null vector is totally isotropic (bilinearly).**  Beyond self-isotropy, the
whole `2`-plane pairs to zero: `Q y z = 0` for all `y, z ∈ span{x, J x}`.  Uses the polarization of
the self-isotropy `null_plane_self_isotropic` (over `ℝ`, `char ≠ 2`). -/
theorem null_plane_totally_isotropic {Q : LinearMap.BilinForm ℝ V}
    (P : PolarizedOmegaComplexStructure V Q) (hQ : Q.IsSymm) {x : V} (hx : Q x x = 0) :
    ∀ y ∈ Submodule.span ℝ ({x, P.complex.J x} : Set V),
      ∀ z ∈ Submodule.span ℝ ({x, P.complex.J x} : Set V), Q y z = 0 := by
  intro y hy z hz
  have hsub : (y + z) ∈ Submodule.span ℝ ({x, P.complex.J x} : Set V) := add_mem hy hz
  have hyz : Q (y + z) (y + z) = 0 := null_plane_self_isotropic P hQ hx _ hsub
  have hyy : Q y y = 0 := null_plane_self_isotropic P hQ hx _ hy
  have hzz : Q z z = 0 := null_plane_self_isotropic P hQ hx _ hz
  have hzy : Q z y = Q y z := hQ.eq z y
  have hexp : Q (y + z) (y + z) = Q y y + Q z z + 2 * Q y z := by
    simp only [map_add, LinearMap.add_apply]; rw [hzy]; ring
  rw [hexp, hyy, hzz] at hyz
  linarith

/-- **A nonzero null vector forces a 2-dimensional totally isotropic subspace.**  Combining
`null_plane_totally_isotropic` with the fact that `x, J x` are independent
(`polarized_negDef_plane_finrank`), a single isotropic direction produces a whole isotropic plane.
A Lorentzian form has Witt index `1` (its maximal totally isotropic subspace is a line), so the seam
form — whenever it has any null vector — is not Lorentzian, read from the light-cone side. -/
theorem null_forces_isotropic_plane {Q : LinearMap.BilinForm ℝ V}
    (P : PolarizedOmegaComplexStructure V Q) (hQ : Q.IsSymm) {x : V} (hx0 : x ≠ 0)
    (hx : Q x x = 0) :
    ∃ W : Submodule ℝ V, Module.finrank ℝ W = 2 ∧
      (∀ w ∈ W, P.complex.J w ∈ W) ∧
      (∀ y ∈ W, ∀ z ∈ W, Q y z = 0) := by
  refine ⟨Submodule.span ℝ ({x, P.complex.J x} : Set V), ?_,
    polarized_plane_Jinvariant P.complex x, null_plane_totally_isotropic P hQ hx⟩
  exact polarized_negDef_plane_finrank P hx0

/-! ### The full inertia triple is even -/

/-- **The seam supermetric is neutral, never Lorentzian.**  Its complete inertia triple
`(sigPos, sigNeg, dim radical)` — the positive index, the negative index (time directions), and the
degeneracy — is `(even, even, even)`: every part comes welded in `J`-pairs.  A Lorentzian metric is
`(n−1, 1, 0)` with an odd, unit negative index; the polarization `J` forbids exactly that. -/
theorem polarized_inertia_triple_even {Q : LinearMap.BilinForm ℝ V} [FiniteDimensional ℝ V]
    (P : PolarizedOmegaComplexStructure V Q) (hQ : Q.IsSymm) :
    Even (sigPos (LinearMap.BilinMap.toQuadraticMap Q)) ∧
      Even (sigNeg (LinearMap.BilinMap.toQuadraticMap Q)) ∧
      Even (Module.finrank ℝ (Q.orthogonal ⊤)) :=
  ⟨polarized_sigPos_even P hQ, polarized_sigNeg_even P hQ, radical_finrank_even P⟩

end RHTower
