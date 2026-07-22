/-
# The polar decomposition `T = U·|T|`

The partial isometry of the polar decomposition, built coordinate-wise from the singular value
decomposition: extend the right singular vectors `fₙ` to a Hilbert basis, and let `U` send `x` to
the vector whose coordinate at the `fₙ`-slot is `⟨eₙ, x⟩` and zero elsewhere.  Bessel's inequality
along the greedy family makes the coordinates square-summable with `‖U x‖ ≤ ‖x‖`; on the greedy
family `U eₙ = fₙ`, and `U` kills the joint orthogonal complement.  Since `|T| eₙ = sₙ eₙ` and
both `T` and `|T|` vanish on the complement of the greedy family, `U ∘ |T|` agrees with `T` on a
Hilbert basis: `T = U ∘L |T|`, and `U` is isometric on the range of `|T|`.

Proved here:
* `polarMap` — the partial isometry `U`, with `norm_polarMap_apply_le` (`‖U x‖ ≤ ‖x‖`),
  `polarMap_apply_svVec` (`U eₙ = fₙ`), and `polarMap_apply_eq_zero_of_orth` (`U` kills the
  orthogonal complement of the greedy family).
* `polarMap_comp_absOp` — **the polar decomposition** `U ∘L |T| = T`.
* `norm_polarMap_absOp_apply` — `U` is isometric on the range of `|T|`.
-/
import GaloisForLFunctions.HTGeometry.SVDExpansion
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix

open scoped InnerProductSpace ComplexConjugate

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →L[ℂ] H}

/-- The right singular vectors extend to a Hilbert basis. -/
theorem exists_svdVec_extension (hcpt : IsCompactOperator T) :
    ∃ (w' : Set H) (b' : HilbertBasis ↥w' ℂ H),
      (svdVec T '' {n | singVal T n ≠ 0}) ⊆ w' ∧ ⇑b' = Subtype.val := by
  classical
  have hA_orth : Orthonormal ℂ
      (Subtype.val : (svdVec T '' {n | singVal T n ≠ 0}) → H) := by
    rw [orthonormal_subtype_iff_ite]
    rintro u ⟨m, hm, rfl⟩ v ⟨n, hn, rfl⟩
    by_cases hmn : m = n
    · subst hmn
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K, norm_svdVec_sq hcpt hm]
      norm_num
    · rw [if_neg fun h => hmn (svdVec_live_injective hcpt hn h),
        inner_svdVec_svdVec_of_ne T hmn]
  obtain ⟨w', b', hAw', hb'⟩ := hA_orth.exists_hilbertBasis_extension
  exact ⟨w', b', hAw', hb'⟩

variable (T) in
/-- The carrier of a Hilbert basis extending the right singular vectors. -/
noncomputable def polarSet (hcpt : IsCompactOperator T) : Set H :=
  (exists_svdVec_extension hcpt).choose

variable (T) in
/-- A Hilbert basis extending the right singular vectors. -/
noncomputable def polarBasis (hcpt : IsCompactOperator T) :
    HilbertBasis ↥(polarSet T hcpt) ℂ H :=
  (exists_svdVec_extension hcpt).choose_spec.choose

variable (T) in
theorem polarSet_subset (hcpt : IsCompactOperator T) :
    svdVec T '' {n | singVal T n ≠ 0} ⊆ polarSet T hcpt :=
  (exists_svdVec_extension hcpt).choose_spec.choose_spec.1

variable (T) in
theorem polarBasis_coe (hcpt : IsCompactOperator T) :
    ⇑(polarBasis T hcpt) = Subtype.val :=
  (exists_svdVec_extension hcpt).choose_spec.choose_spec.2

open Classical in
variable (T) in
/-- The coordinates of the polar partial isometry: `⟨eₙ, x⟩` at the `fₙ`-slot, zero elsewhere. -/
noncomputable def polarCoeff (hcpt : IsCompactOperator T) (x : H) :
    ↥(polarSet T hcpt) → ℂ := fun v' =>
  if h : ∃ n, singVal T n ≠ 0 ∧ svdVec T n = ↑v'
  then inner ℂ (svVec (energyOp T) h.choose) x else 0

theorem polarCoeff_apply_of_eq (hcpt : IsCompactOperator T) (x : H) {n : ℕ}
    (hn : singVal T n ≠ 0) {v' : ↥(polarSet T hcpt)} (hv : (v' : H) = svdVec T n) :
    polarCoeff T hcpt x v' = inner ℂ (svVec (energyOp T) n) x := by
  have hex : ∃ m, singVal T m ≠ 0 ∧ svdVec T m = (v' : H) := ⟨n, hn, hv.symm⟩
  rw [polarCoeff, dif_pos hex]
  have hspec := hex.choose_spec
  have heq : hex.choose = n :=
    svdVec_live_injective hcpt hn (by rw [hspec.2, hv])
  rw [heq]

theorem polarCoeff_apply_of_notMem (hcpt : IsCompactOperator T) (x : H)
    {v' : ↥(polarSet T hcpt)} (hv : (v' : H) ∉ svdVec T '' {n | singVal T n ≠ 0}) :
    polarCoeff T hcpt x v' = 0 := by
  rw [polarCoeff, dif_neg]
  rintro ⟨n, hn, h⟩
  exact hv ⟨n, hn, h⟩

theorem summable_polarCoeff_sq (hcpt : IsCompactOperator T) (x : H) :
    Summable (fun v' : ↥(polarSet T hcpt) => ‖polarCoeff T hcpt x v'‖ ^ 2) := by
  classical
  set i : {n : ℕ // singVal T n ≠ 0} → ↥(polarSet T hcpt) :=
    fun p => ⟨svdVec T p.1, polarSet_subset T hcpt ⟨p.1, p.2, rfl⟩⟩ with hi_def
  have hi : Function.Injective i := by
    rintro ⟨m, hm⟩ ⟨n, hn⟩ h
    exact Subtype.ext (svdVec_live_injective hcpt hn (congrArg Subtype.val h))
  have hoff : ∀ v' ∉ Set.range i, ‖polarCoeff T hcpt x v'‖ ^ 2 = 0 := by
    intro v' hv
    have hnotMem : (v' : H) ∉ svdVec T '' {n | singVal T n ≠ 0} := by
      rintro ⟨n, hn, h⟩
      exact hv ⟨⟨n, hn⟩, Subtype.ext h⟩
    rw [polarCoeff_apply_of_notMem hcpt x hnotMem]
    simp
  refine (hi.summable_iff hoff).mp ?_
  have hcomp : ((fun v' => ‖polarCoeff T hcpt x v'‖ ^ 2) ∘ i)
      = fun p : {n : ℕ // singVal T n ≠ 0} =>
          ‖inner ℂ (svVec (energyOp T) p.1) x‖ ^ 2 := by
    funext p
    show ‖polarCoeff T hcpt x (i p)‖ ^ 2 = _
    rw [polarCoeff_apply_of_eq hcpt x p.2 rfl]
  rw [hcomp]
  exact (summable_inner_svVec_sq hcpt x).subtype _

variable (T) in
/-- The polar coordinates as an `ℓ²` element. -/
noncomputable def polarLp (hcpt : IsCompactOperator T) (x : H) :
    lp (fun _ : ↥(polarSet T hcpt) => ℂ) 2 :=
  ⟨polarCoeff T hcpt x, HilbertSchmidt.memℓp_of_sq (summable_polarCoeff_sq hcpt x)⟩

theorem norm_polarLp_sq_le (hcpt : IsCompactOperator T) (x : H) :
    ‖polarLp T hcpt x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  classical
  rw [HilbertSchmidt.lp_norm_sq_eq]
  show ∑' v' : ↥(polarSet T hcpt), ‖polarCoeff T hcpt x v'‖ ^ 2 ≤ ‖x‖ ^ 2
  have htrans : ∑' v' : ↥(polarSet T hcpt), ‖polarCoeff T hcpt x v'‖ ^ 2
      = ∑' p : {n : ℕ // singVal T n ≠ 0},
          ‖inner ℂ (svVec (energyOp T) p.1) x‖ ^ 2 := by
    refine tsum_eq_tsum_of_ne_zero_bij
      (fun p => ⟨svdVec T p.1.1, polarSet_subset T hcpt ⟨p.1.1, p.1.2, rfl⟩⟩) ?_ ?_ ?_
    · rintro ⟨⟨m, hm⟩, hm'⟩ ⟨⟨n, hn⟩, hn'⟩ h
      exact Subtype.ext (Subtype.ext
        (svdVec_live_injective hcpt hn (congrArg Subtype.val h)))
    · rintro v' hv'
      rw [Function.mem_support] at hv'
      have hmem : (v' : H) ∈ svdVec T '' {n | singVal T n ≠ 0} := by
        by_contra hnot
        rw [polarCoeff_apply_of_notMem hcpt x hnot] at hv'
        simp at hv'
      obtain ⟨n, hn, hvn⟩ := hmem
      have hval : polarCoeff T hcpt x v' = inner ℂ (svVec (energyOp T) n) x :=
        polarCoeff_apply_of_eq hcpt x hn hvn.symm
      have hgn : ‖inner ℂ (svVec (energyOp T) n) x‖ ^ 2 ≠ 0 := by
        rw [← hval]
        exact hv'
      exact ⟨⟨⟨n, hn⟩, hgn⟩, Subtype.ext hvn⟩
    · rintro ⟨⟨n, hn⟩, hn'⟩
      show ‖polarCoeff T hcpt x _‖ ^ 2 = _
      rw [polarCoeff_apply_of_eq hcpt x hn rfl]
  rw [htrans]
  have hsub : ∑' p : {n : ℕ // singVal T n ≠ 0},
        ‖inner ℂ (svVec (energyOp T) p.1) x‖ ^ 2
      = ∑' n : ℕ, ‖inner ℂ (svVec (energyOp T) n) x‖ ^ 2 := by
    refine tsum_subtype_eq_of_support_subset
      (f := fun n => ‖inner ℂ (svVec (energyOp T) n) x‖ ^ 2)
      (s := {n | singVal T n ≠ 0}) ?_
    intro n hn
    by_contra h0
    simp only [Set.mem_setOf_eq, not_not] at h0
    have hdead : svVal (energyOp T) n = 0 := by
      by_contra hμ
      exact hμ (by rw [← singVal_sq T n, h0]; ring)
    rw [Function.mem_support, svVec_eq_zero_of_svVal_eq_zero _ hdead] at hn
    simp at hn
  rw [hsub]
  exact tsum_inner_svVec_sq_le hcpt x

variable (T) in
/-- **The polar partial isometry** `U`: coordinates `⟨eₙ, x⟩` at the `fₙ`-slots of a Hilbert
basis extending the right singular vectors. -/
noncomputable def polarMap (hcpt : IsCompactOperator T) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun x => (polarBasis T hcpt).repr.symm (polarLp T hcpt x)
      map_add' := fun x y => by
        rw [← map_add]
        congr 1
        apply lp.ext
        funext v'
        rw [lp.coeFn_add, Pi.add_apply]
        show polarCoeff T hcpt (x + y) v'
          = polarCoeff T hcpt x v' + polarCoeff T hcpt y v'
        rw [polarCoeff, polarCoeff, polarCoeff]
        split_ifs with h
        · rw [inner_add_right]
        · rw [add_zero]
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        rw [← map_smul]
        congr 1
        apply lp.ext
        funext v'
        rw [lp.coeFn_smul, Pi.smul_apply]
        show polarCoeff T hcpt (c • x) v' = c • polarCoeff T hcpt x v'
        rw [polarCoeff, polarCoeff]
        split_ifs with h
        · rw [inner_smul_right, smul_eq_mul]
        · rw [smul_zero] }
    1
    (fun x => by
      show ‖(polarBasis T hcpt).repr.symm (polarLp T hcpt x)‖ ≤ 1 * ‖x‖
      rw [one_mul, LinearIsometryEquiv.norm_map]
      have h2 := norm_polarLp_sq_le hcpt x
      nlinarith [norm_nonneg (polarLp T hcpt x), norm_nonneg x])

theorem polarMap_apply (hcpt : IsCompactOperator T) (x : H) :
    polarMap T hcpt x = (polarBasis T hcpt).repr.symm (polarLp T hcpt x) := rfl

/-- `‖U x‖ ≤ ‖x‖`: the polar map is a contraction. -/
theorem norm_polarMap_apply_le (hcpt : IsCompactOperator T) (x : H) :
    ‖polarMap T hcpt x‖ ≤ ‖x‖ := by
  rw [polarMap_apply, LinearIsometryEquiv.norm_map]
  have h2 := norm_polarLp_sq_le hcpt x
  nlinarith [norm_nonneg (polarLp T hcpt x), norm_nonneg x]

/-- `U eₙ = fₙ`: the polar map carries the greedy eigenbasis to the right singular vectors. -/
theorem polarMap_apply_svVec (hcpt : IsCompactOperator T) {n : ℕ} (hn : singVal T n ≠ 0) :
    polarMap T hcpt (svVec (energyOp T) n) = svdVec T n := by
  classical
  have hμ : svVal (energyOp T) n ≠ 0 := by
    intro h
    exact hn (by rw [singVal, h, Real.sqrt_zero])
  set slot : ↥(polarSet T hcpt) :=
    ⟨svdVec T n, polarSet_subset T hcpt ⟨n, hn, rfl⟩⟩ with hslot
  have hlp : polarLp T hcpt (svVec (energyOp T) n) = lp.single 2 slot 1 := by
    apply lp.ext
    funext v'
    by_cases hv : v' = slot
    · subst hv
      rw [lp.single_apply_self]
      show polarCoeff T hcpt (svVec (energyOp T) n) slot = 1
      rw [polarCoeff_apply_of_eq hcpt _ hn rfl, inner_self_eq_norm_sq_to_K,
        norm_svVec_of_ne_zero (energyOp_compact hcpt) (energyOp_symmetric T)
          (energyOp_pos T) hμ]
      norm_num
    · rw [lp.single_apply_ne _ _ _ hv]
      show polarCoeff T hcpt (svVec (energyOp T) n) v' = 0
      by_cases him : (v' : H) ∈ svdVec T '' {m | singVal T m ≠ 0}
      · obtain ⟨m, hm, hvm⟩ := him
        rw [polarCoeff_apply_of_eq hcpt _ hm hvm.symm]
        by_cases hmn : m = n
        · exfalso
          apply hv
          subst hmn
          exact Subtype.ext hvm.symm
        · exact inner_svVec_svVec_of_ne (energyOp T) hmn
      · exact polarCoeff_apply_of_notMem hcpt _ him
  rw [polarMap_apply, hlp, HilbertBasis.repr_symm_single]
  rw [show polarBasis T hcpt slot = (slot : H) from congrFun (polarBasis_coe T hcpt) slot]

/-- `U` kills the joint orthogonal complement of the greedy family. -/
theorem polarMap_apply_eq_zero_of_orth (hcpt : IsCompactOperator T) {x : H}
    (hx : ∀ n, inner ℂ (svVec (energyOp T) n) x = 0) : polarMap T hcpt x = 0 := by
  rw [polarMap_apply]
  have hc : polarLp T hcpt x = 0 := by
    apply lp.ext
    funext v'
    show polarCoeff T hcpt x v' = (0 : lp (fun _ : ↥(polarSet T hcpt) => ℂ) 2) v'
    have h0 : (0 : lp (fun _ : ↥(polarSet T hcpt) => ℂ) 2) v' = 0 := rfl
    rw [h0]
    by_cases him : (v' : H) ∈ svdVec T '' {m | singVal T m ≠ 0}
    · obtain ⟨m, hm, hvm⟩ := him
      rw [polarCoeff_apply_of_eq hcpt x hm hvm.symm]
      exact hx m
    · exact polarCoeff_apply_of_notMem hcpt x him
  rw [hc, map_zero]

/-- **The polar decomposition.**  `U ∘L |T| = T`: the two sides agree on the greedy family — where
`|T| eₙ = sₙ eₙ`, `U eₙ = fₙ`, and `T eₙ = sₙ fₙ` — and both kill its orthogonal complement. -/
theorem polarMap_comp_absOp (hcpt : IsCompactOperator T) :
    polarMap T hcpt ∘L absOp T = T := by
  classical
  obtain ⟨w, b, hAw, hb⟩ := exists_svVec_extension hcpt
  have hdense : Dense (↑(Submodule.span ℂ w) : Set H) := by
    refine Submodule.dense_iff_topologicalClosure_eq_top.mpr ?_
    have hd := b.dense_span
    rwa [hb, Subtype.range_coe] at hd
  refine ContinuousLinearMap.ext_on hdense ?_
  intro v hv
  by_cases hvA : v ∈ svVec (energyOp T) '' {n | svVal (energyOp T) n ≠ 0}
  · obtain ⟨n, hn, rfl⟩ := hvA
    have hsn : singVal T n ≠ 0 := fun h => hn (by rw [← singVal_sq T n, h]; ring)
    rw [comp_apply, absOp_apply_svVec, map_smul, polarMap_apply_svVec hcpt hsn,
      ← apply_svVec_eq_smul_svdVec]
  · have horthw : ∀ u ∈ w, ∀ z ∈ w, u ≠ z → inner ℂ u z = 0 := by
      have hw_orth : Orthonormal ℂ (Subtype.val : w → H) := hb ▸ b.orthonormal
      rw [orthonormal_subtype_iff_ite] at hw_orth
      intro u hu z hz huz
      have h2 := hw_orth u hu z hz
      rwa [if_neg huz] at h2
    have horth : ∀ m, inner ℂ (svVec (energyOp T) m) v = 0 := by
      intro m
      rcases eq_or_ne (svVal (energyOp T) m) 0 with h0 | hne0
      · rw [svVec_eq_zero_of_svVal_eq_zero (energyOp T) h0]
        exact inner_zero_left _
      · have hmem : svVec (energyOp T) m ∈ w := hAw ⟨m, hne0, rfl⟩
        refine horthw _ hmem _ hv fun h => hvA ?_
        rw [← h]
        exact ⟨m, hne0, rfl⟩
    have hTv : T v = 0 := apply_eq_zero_of_forall_inner_svVec_energyOp hcpt horth
    have hAv : absOp T v = 0 := by
      have h1 : ‖absOp T v‖ = ‖T v‖ := norm_absOp_apply T v
      rw [hTv, norm_zero] at h1
      exact norm_eq_zero.mp h1
    rw [comp_apply, hAv, map_zero, hTv]

/-- **`U` is isometric on the range of `|T|`**: `‖U(|T| x)‖ = ‖|T| x‖`. -/
theorem norm_polarMap_absOp_apply (hcpt : IsCompactOperator T) (x : H) :
    ‖polarMap T hcpt (absOp T x)‖ = ‖absOp T x‖ := by
  have h1 : polarMap T hcpt (absOp T x) = T x := by
    rw [← comp_apply, polarMap_comp_absOp hcpt]
  rw [h1, ← norm_absOp_apply]

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →L[ℂ] H}

/-- Pairing a basis vector against a reconstructed element reads off the coordinate. -/
theorem inner_polarBasis_repr_symm (hcpt : IsCompactOperator T)
    (c : lp (fun _ : ↥(polarSet T hcpt) => ℂ) 2) (slot : ↥(polarSet T hcpt)) :
    inner ℂ ((slot : H)) ((polarBasis T hcpt).repr.symm c) = c slot := by
  have h1 := HilbertBasis.repr_apply_apply (polarBasis T hcpt)
    ((polarBasis T hcpt).repr.symm c) slot
  rw [LinearIsometryEquiv.apply_symm_apply] at h1
  rw [show ((slot : H)) = polarBasis T hcpt slot
    from (congrFun (polarBasis_coe T hcpt) slot).symm]
  exact h1.symm

/-- The adjoint of the polar map carries the right singular vectors back:
`U† fₙ = eₙ`. -/
theorem adjoint_polarMap_apply_svdVec (hcpt : IsCompactOperator T) {n : ℕ}
    (hn : singVal T n ≠ 0) :
    ContinuousLinearMap.adjoint (polarMap T hcpt) (svdVec T n)
      = svVec (energyOp T) n := by
  refine ext_inner_right ℂ fun y => ?_
  rw [adjoint_inner_left, polarMap_apply]
  have h1 := inner_polarBasis_repr_symm hcpt (polarLp T hcpt y)
    ⟨svdVec T n, polarSet_subset T hcpt ⟨n, hn, rfl⟩⟩
  exact h1.trans (polarCoeff_apply_of_eq hcpt y hn rfl)

/-- **The reverse polar factorization**: `U† ∘L T = |T|`. -/
theorem adjoint_polarMap_comp_eq_absOp (hcpt : IsCompactOperator T) :
    ContinuousLinearMap.adjoint (polarMap T hcpt) ∘L T = absOp T := by
  classical
  obtain ⟨w, b, hAw, hb⟩ := exists_svVec_extension hcpt
  have hdense : Dense (↑(Submodule.span ℂ w) : Set H) := by
    refine Submodule.dense_iff_topologicalClosure_eq_top.mpr ?_
    have hd := b.dense_span
    rwa [hb, Subtype.range_coe] at hd
  refine ContinuousLinearMap.ext_on hdense ?_
  intro v hv
  by_cases hvA : v ∈ svVec (energyOp T) '' {n | svVal (energyOp T) n ≠ 0}
  · obtain ⟨n, hn, rfl⟩ := hvA
    have hsn : singVal T n ≠ 0 := fun h => hn (by rw [← singVal_sq T n, h]; ring)
    rw [comp_apply, apply_svVec_eq_smul_svdVec, map_smul,
      adjoint_polarMap_apply_svdVec hcpt hsn, absOp_apply_svVec]
  · have horthw : ∀ u ∈ w, ∀ z ∈ w, u ≠ z → inner ℂ u z = 0 := by
      have hw_orth : Orthonormal ℂ (Subtype.val : w → H) := hb ▸ b.orthonormal
      rw [orthonormal_subtype_iff_ite] at hw_orth
      intro u hu z hz huz
      have h2 := hw_orth u hu z hz
      rwa [if_neg huz] at h2
    have horth : ∀ m, inner ℂ (svVec (energyOp T) m) v = 0 := by
      intro m
      rcases eq_or_ne (svVal (energyOp T) m) 0 with h0 | hne0
      · rw [svVec_eq_zero_of_svVal_eq_zero (energyOp T) h0]
        exact inner_zero_left _
      · have hmem : svVec (energyOp T) m ∈ w := hAw ⟨m, hne0, rfl⟩
        refine horthw _ hmem _ hv fun h => hvA ?_
        rw [← h]
        exact ⟨m, hne0, rfl⟩
    have hTv : T v = 0 := apply_eq_zero_of_forall_inner_svVec_energyOp hcpt horth
    have hAv : absOp T v = 0 := by
      have h1 : ‖absOp T v‖ = ‖T v‖ := norm_absOp_apply T v
      rw [hTv, norm_zero] at h1
      exact norm_eq_zero.mp h1
    rw [comp_apply, hTv, map_zero, hAv]

/-- `U†U` fixes the greedy family. -/
theorem adjoint_polarMap_polarMap_apply_svVec (hcpt : IsCompactOperator T) {n : ℕ}
    (hμ : svVal (energyOp T) n ≠ 0) :
    ContinuousLinearMap.adjoint (polarMap T hcpt) (polarMap T hcpt (svVec (energyOp T) n))
      = svVec (energyOp T) n := by
  have hsn : singVal T n ≠ 0 := fun h => hμ (by rw [← singVal_sq T n, h]; ring)
  rw [polarMap_apply_svVec hcpt hsn, adjoint_polarMap_apply_svdVec hcpt hsn]

/-- `U†U` kills the joint orthogonal complement of the greedy family. -/
theorem adjoint_polarMap_polarMap_apply_eq_zero_of_orth (hcpt : IsCompactOperator T) {x : H}
    (hx : ∀ n, inner ℂ (svVec (energyOp T) n) x = 0) :
    ContinuousLinearMap.adjoint (polarMap T hcpt) (polarMap T hcpt x) = 0 := by
  rw [polarMap_apply_eq_zero_of_orth hcpt hx, map_zero]

/-- `U†U` is self-adjoint. -/
theorem adjoint_adjoint_polarMap_comp_polarMap (hcpt : IsCompactOperator T) :
    ContinuousLinearMap.adjoint
        (ContinuousLinearMap.adjoint (polarMap T hcpt) ∘L polarMap T hcpt)
      = ContinuousLinearMap.adjoint (polarMap T hcpt) ∘L polarMap T hcpt := by
  rw [adjoint_comp, adjoint_adjoint]

/-- **`U†U` is the orthogonal projection onto the closed span of the greedy family**: it is a
self-adjoint idempotent fixing each greedy vector and killing their joint orthogonal
complement. -/
theorem adjoint_polarMap_comp_polarMap_idempotent (hcpt : IsCompactOperator T) :
    (ContinuousLinearMap.adjoint (polarMap T hcpt) ∘L polarMap T hcpt)
        ∘L (ContinuousLinearMap.adjoint (polarMap T hcpt) ∘L polarMap T hcpt)
      = ContinuousLinearMap.adjoint (polarMap T hcpt) ∘L polarMap T hcpt := by
  classical
  obtain ⟨w, b, hAw, hb⟩ := exists_svVec_extension hcpt
  have hdense : Dense (↑(Submodule.span ℂ w) : Set H) := by
    refine Submodule.dense_iff_topologicalClosure_eq_top.mpr ?_
    have hd := b.dense_span
    rwa [hb, Subtype.range_coe] at hd
  refine ContinuousLinearMap.ext_on hdense ?_
  intro v hv
  by_cases hvA : v ∈ svVec (energyOp T) '' {n | svVal (energyOp T) n ≠ 0}
  · obtain ⟨n, hn, rfl⟩ := hvA
    simp only [comp_apply]
    rw [adjoint_polarMap_polarMap_apply_svVec hcpt hn,
      adjoint_polarMap_polarMap_apply_svVec hcpt hn]
  · have horthw : ∀ u ∈ w, ∀ z ∈ w, u ≠ z → inner ℂ u z = 0 := by
      have hw_orth : Orthonormal ℂ (Subtype.val : w → H) := hb ▸ b.orthonormal
      rw [orthonormal_subtype_iff_ite] at hw_orth
      intro u hu z hz huz
      have h2 := hw_orth u hu z hz
      rwa [if_neg huz] at h2
    have horth : ∀ m, inner ℂ (svVec (energyOp T) m) v = 0 := by
      intro m
      rcases eq_or_ne (svVal (energyOp T) m) 0 with h0 | hne0
      · rw [svVec_eq_zero_of_svVal_eq_zero (energyOp T) h0]
        exact inner_zero_left _
      · have hmem : svVec (energyOp T) m ∈ w := hAw ⟨m, hne0, rfl⟩
        refine horthw _ hmem _ hv fun h => hvA ?_
        rw [← h]
        exact ⟨m, hne0, rfl⟩
    have hUv : ContinuousLinearMap.adjoint (polarMap T hcpt) (polarMap T hcpt v) = 0 :=
      adjoint_polarMap_polarMap_apply_eq_zero_of_orth hcpt horth
    simp only [comp_apply]
    rw [hUv, map_zero, map_zero]

end ContinuousLinearMap
