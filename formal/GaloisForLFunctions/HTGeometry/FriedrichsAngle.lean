import GaloisForLFunctions.HTGeometry.ConstraintLaplacian

/-!
# The Friedrichs angle and the sharp pairwise precision law

For two closed subspaces `U, V` of a Hilbert space with `W = U ⊓ V`, the **Friedrichs cosine**

`c_F(U,V) = sup {‖⟪u, v⟫‖ : u ∈ U ⊖ W, v ∈ V ⊖ W, ‖u‖ = ‖v‖ = 1}`

controls the total precision defect exactly:

* `pair_precision_lower_bound` : `dist(x,U)² + dist(x,V)² ≥ (1 − c_F)‖x‖²` for every `x ⊥ W`;
* `exists_transverse_unit_pairPrecision_le` : the constant `1 − c_F` cannot be improved once the
  generic part `U ⊖ W` is nontrivial.  That hypothesis is necessary: for `U = V` both generic
  parts vanish, `c_F = 0`, and the transverse defect is `2‖x‖²`;
* `one_sharp_tradeoff` : if `x ∈ U ⊖ W` then `dist(x,V)² ≥ (1 − c_F²)‖x‖²`.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- The set of pairwise cosines of unit vectors in the two generic parts. -/
def friedrichsCosineSet (U V : Submodule 𝕜 H) : Set ℝ :=
  {r : ℝ | ∃ u ∈ U ⊓ (U ⊓ V)ᗮ, ∃ v ∈ V ⊓ (U ⊓ V)ᗮ, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ r = ‖⟪u, v⟫_𝕜‖}

/-- The **Friedrichs cosine** of a pair of closed subspaces. -/
noncomputable def friedrichsCosine (U V : Submodule 𝕜 H) : ℝ :=
  sSup (friedrichsCosineSet U V)

/-- The total precision defect of the pair `(U, V)` at `x`. -/
noncomputable def pairPrecision (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (x : H) : ℝ :=
  ‖x - U.starProjection x‖ ^ (2 : ℕ) + ‖x - V.starProjection x‖ ^ (2 : ℕ)

omit [CompleteSpace H] in
theorem friedrichsCosineSet_subset_Icc (U V : Submodule 𝕜 H) :
    friedrichsCosineSet U V ⊆ Set.Icc (0 : ℝ) 1 := by
  rintro r ⟨u, _, v, _, hu, hv, rfl⟩
  refine ⟨norm_nonneg _, ?_⟩
  calc ‖⟪u, v⟫_𝕜‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
    _ = 1 := by rw [hu, hv, one_mul]

omit [CompleteSpace H] in
theorem friedrichsCosineSet_bddAbove (U V : Submodule 𝕜 H) :
    BddAbove (friedrichsCosineSet U V) :=
  ⟨1, fun _ hr => (friedrichsCosineSet_subset_Icc U V hr).2⟩

omit [CompleteSpace H] in
theorem friedrichsCosine_nonneg (U V : Submodule 𝕜 H) : 0 ≤ friedrichsCosine U V :=
  Real.sSup_nonneg fun _ hr => (friedrichsCosineSet_subset_Icc U V hr).1

omit [CompleteSpace H] in
theorem friedrichsCosine_le_one (U V : Submodule 𝕜 H) : friedrichsCosine U V ≤ 1 :=
  Real.sSup_le (fun _ hr => (friedrichsCosineSet_subset_Icc U V hr).2) zero_le_one

omit [CompleteSpace H] in
/-- The defining bound: on the generic parts the pairing is contracted by the Friedrichs
cosine. -/
theorem norm_inner_le_friedrichsCosine (U V : Submodule 𝕜 H)
    {u v : H} (hu : u ∈ U ⊓ (U ⊓ V)ᗮ) (hv : v ∈ V ⊓ (U ⊓ V)ᗮ) :
    ‖⟪u, v⟫_𝕜‖ ≤ friedrichsCosine U V * ‖u‖ * ‖v‖ := by
  rcases eq_or_ne u 0 with rfl | hu0
  · simp
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have hun : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
  have hvn : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
  set u' : H := (‖u‖ : 𝕜)⁻¹ • u with hu'
  set v' : H := (‖v‖ : 𝕜)⁻¹ • v with hv'
  have hu'mem : u' ∈ U ⊓ (U ⊓ V)ᗮ := Submodule.smul_mem _ _ hu
  have hv'mem : v' ∈ V ⊓ (U ⊓ V)ᗮ := Submodule.smul_mem _ _ hv
  have hu'norm : ‖u'‖ = 1 := by
    rw [hu', norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg hun.le,
      inv_mul_cancel₀ hun.ne']
  have hv'norm : ‖v'‖ = 1 := by
    rw [hv', norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg hvn.le,
      inv_mul_cancel₀ hvn.ne']
  have hmem : ‖⟪u', v'⟫_𝕜‖ ∈ friedrichsCosineSet U V :=
    ⟨u', hu'mem, v', hv'mem, hu'norm, hv'norm, rfl⟩
  have hle : ‖⟪u', v'⟫_𝕜‖ ≤ friedrichsCosine U V :=
    le_csSup (friedrichsCosineSet_bddAbove U V) hmem
  have hval : ‖⟪u', v'⟫_𝕜‖ = ‖u‖⁻¹ * ‖v‖⁻¹ * ‖⟪u, v⟫_𝕜‖ := by
    rw [hu', hv', inner_smul_left, inner_smul_right, norm_mul, norm_mul, RCLike.norm_conj,
      norm_inv, norm_inv, RCLike.norm_ofReal, RCLike.norm_ofReal,
      abs_of_nonneg hun.le, abs_of_nonneg hvn.le]
    ring
  rw [hval] at hle
  have hmul := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ ‖u‖ * ‖v‖)
  calc ‖⟪u, v⟫_𝕜‖ = ‖u‖ * ‖v‖ * (‖u‖⁻¹ * ‖v‖⁻¹ * ‖⟪u, v⟫_𝕜‖) := by field_simp
    _ ≤ ‖u‖ * ‖v‖ * friedrichsCosine U V := hmul
    _ = friedrichsCosine U V * ‖u‖ * ‖v‖ := by ring

section Closed

variable {U V : Submodule 𝕜 H} (hU : IsClosed (U : Set H)) (hV : IsClosed (V : Set H))

include hU in
theorem starProjection_mem_genericPart (x : H) (hx : x ∈ ((U ⊓ V)ᗮ : Submodule 𝕜 H)) :
    U.starProjection x ∈ U ⊓ (U ⊓ V)ᗮ := by
  haveI : CompleteSpace U := hU.completeSpace_coe
  refine Submodule.mem_inf.mpr ⟨U.starProjection_apply_mem x, ?_⟩
  refine (Submodule.mem_orthogonal _ _).mpr ?_
  intro w hw
  have hPw : U.starProjection w = w := U.starProjection_eq_self_iff.mpr hw.1
  have hsym : ⟪U.starProjection w, x⟫_𝕜 = ⟪w, U.starProjection x⟫_𝕜 :=
    U.starProjection_isSymmetric w x
  rw [← hsym, hPw]
  exact (Submodule.mem_orthogonal _ x).mp hx w hw

include hU in
theorem norm_sub_starProjection_sq (x : H) :
    ‖x - U.starProjection x‖ ^ (2 : ℕ) = ‖x‖ ^ (2 : ℕ) - ‖U.starProjection x‖ ^ (2 : ℕ) := by
  haveI : CompleteSpace U := hU.completeSpace_coe
  have hsplit : x - U.starProjection x = Uᗮ.starProjection x := by
    rw [eq_comm, eq_sub_iff_add_eq, add_comm]
    exact U.starProjection_add_starProjection_orthogonal x
  rw [hsplit, U.norm_sq_eq_add_norm_sq_starProjection x]
  ring

include hU in
theorem inner_starProjection_self (x : H) :
    ⟪U.starProjection x, x⟫_𝕜 = ⟪U.starProjection x, U.starProjection x⟫_𝕜 := by
  haveI : CompleteSpace U := hU.completeSpace_coe
  have hzero : ⟪x - U.starProjection x, U.starProjection x⟫_𝕜 = 0 :=
    U.starProjection_inner_eq_zero x _ (U.starProjection_apply_mem x)
  have hconj : ⟪U.starProjection x, x - U.starProjection x⟫_𝕜 = 0 := by
    rw [← inner_conj_symm, hzero, map_zero]
  have hsplit : ⟪U.starProjection x, x⟫_𝕜
      = ⟪U.starProjection x, U.starProjection x⟫_𝕜
        + ⟪U.starProjection x, x - U.starProjection x⟫_𝕜 := by
    rw [← inner_add_right]
    congr 1
    abel
  rw [hsplit, hconj, add_zero]

include hU in
theorem norm_starProjection_le_of_inner (x : H) {w : H} (hw : w ∈ U) (hwn : ‖w‖ = 1) :
    ‖⟪x, w⟫_𝕜‖ ≤ ‖U.starProjection x‖ := by
  haveI : CompleteSpace U := hU.completeSpace_coe
  have hPw : U.starProjection w = w := U.starProjection_eq_self_iff.mpr hw
  have hsym : ⟪U.starProjection x, w⟫_𝕜 = ⟪x, U.starProjection w⟫_𝕜 :=
    U.starProjection_isSymmetric x w
  rw [hPw] at hsym
  calc ‖⟪x, w⟫_𝕜‖ = ‖⟪U.starProjection x, w⟫_𝕜‖ := by rw [hsym]
    _ ≤ ‖U.starProjection x‖ * ‖w‖ := norm_inner_le_norm _ _
    _ = ‖U.starProjection x‖ := by rw [hwn, mul_one]

include hU hV in
theorem pairPrecision_smul (c : 𝕜) (x : H) :
    haveI : CompleteSpace U := hU.completeSpace_coe
    haveI : CompleteSpace V := hV.completeSpace_coe
    pairPrecision U V (c • x) = ‖c‖ ^ (2 : ℕ) * pairPrecision U V x := by
  haveI : CompleteSpace U := hU.completeSpace_coe
  haveI : CompleteSpace V := hV.completeSpace_coe
  have hU' : c • x - U.starProjection (c • x) = c • (x - U.starProjection x) := by
    rw [map_smul, smul_sub]
  have hV' : c • x - V.starProjection (c • x) = c • (x - V.starProjection x) := by
    rw [map_smul, smul_sub]
  rw [pairPrecision, pairPrecision, hU', hV', norm_smul, norm_smul]
  ring

include hU hV in
/-- **The sharp pairwise precision law.**  Every transverse presentation pays at least the
Friedrichs precision cost. -/
theorem pair_precision_lower_bound (x : H) (hx : x ∈ ((U ⊓ V)ᗮ : Submodule 𝕜 H)) :
    haveI : CompleteSpace U := hU.completeSpace_coe
    haveI : CompleteSpace V := hV.completeSpace_coe
    (1 - friedrichsCosine U V) * ‖x‖ ^ (2 : ℕ) ≤ pairPrecision U V x := by
  haveI : CompleteSpace U := hU.completeSpace_coe
  haveI : CompleteSpace V := hV.completeSpace_coe
  set c : ℝ := friedrichsCosine U V with hc
  set a : H := U.starProjection x with hadef
  set b : H := V.starProjection x with hbdef
  have hamem : a ∈ U ⊓ (U ⊓ V)ᗮ := starProjection_mem_genericPart hU x hx
  have hUV : (V ⊓ U : Submodule 𝕜 H) = U ⊓ V := inf_comm V U
  have hbmem : b ∈ V ⊓ (U ⊓ V)ᗮ := by
    have hx' : x ∈ ((V ⊓ U)ᗮ : Submodule 𝕜 H) := by rw [hUV]; exact hx
    have hmem := starProjection_mem_genericPart hV x hx'
    rw [hUV] at hmem
    exact hmem
  have hab : ‖⟪a, b⟫_𝕜‖ ≤ c * ‖a‖ * ‖b‖ := norm_inner_le_friedrichsCosine U V hamem hbmem
  have hcnn : 0 ≤ c := friedrichsCosine_nonneg U V
  set s : ℝ := ‖a‖ ^ (2 : ℕ) + ‖b‖ ^ (2 : ℕ) with hs
  have hsnn : 0 ≤ s := by positivity
  have hax : RCLike.re (⟪a, x⟫_𝕜) = ‖a‖ ^ (2 : ℕ) := by
    rw [hadef, inner_starProjection_self hU x, inner_self_eq_norm_sq]
  have hbx : RCLike.re (⟪b, x⟫_𝕜) = ‖b‖ ^ (2 : ℕ) := by
    rw [hbdef, inner_starProjection_self hV x, inner_self_eq_norm_sq]
  have hsum : RCLike.re (⟪a + b, x⟫_𝕜) = s := by
    rw [inner_add_left, map_add, hax, hbx]
  have hs_le : s ≤ ‖a + b‖ * ‖x‖ := by
    rw [← hsum]
    exact le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)
  have hnorm_add : ‖a + b‖ ^ (2 : ℕ) ≤ (1 + c) * s := by
    have hexp : ‖a + b‖ ^ (2 : ℕ) = ‖a‖ ^ (2 : ℕ) + 2 * RCLike.re (⟪a, b⟫_𝕜) + ‖b‖ ^ (2 : ℕ) :=
      norm_add_sq (𝕜 := 𝕜) a b
    have hre : RCLike.re (⟪a, b⟫_𝕜) ≤ c * ‖a‖ * ‖b‖ := le_trans (RCLike.re_le_norm _) hab
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), hcnn]
  have hsbound : s ≤ (1 + c) * ‖x‖ ^ (2 : ℕ) := by
    rcases eq_or_lt_of_le hsnn with hzero | hpos
    · nlinarith [sq_nonneg ‖x‖]
    · have h1 : s ^ (2 : ℕ) ≤ (‖a + b‖ * ‖x‖) ^ (2 : ℕ) := by nlinarith [norm_nonneg (a + b), norm_nonneg x]
      have h3 : ‖a + b‖ ^ (2 : ℕ) * ‖x‖ ^ (2 : ℕ) ≤ (1 + c) * s * ‖x‖ ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hnorm_add (sq_nonneg _)
      nlinarith
  rw [pairPrecision, norm_sub_starProjection_sq hU x, norm_sub_starProjection_sq hV x,
    ← hadef, ← hbdef]
  nlinarith

include hV in
/-- **The one-sharp tradeoff.**  A vector exactly accepted by the first observer is at distance
at least `√(1 − c_F²)` from the second observer's sector. -/
theorem one_sharp_tradeoff (x : H) (hx : x ∈ U ⊓ ((U ⊓ V)ᗮ : Submodule 𝕜 H)) :
    haveI : CompleteSpace V := hV.completeSpace_coe
    (1 - friedrichsCosine U V ^ (2 : ℕ)) * ‖x‖ ^ (2 : ℕ) ≤ ‖x - V.starProjection x‖ ^ (2 : ℕ) := by
  haveI : CompleteSpace V := hV.completeSpace_coe
  set c : ℝ := friedrichsCosine U V with hc
  have hcnn : 0 ≤ c := friedrichsCosine_nonneg U V
  have hUV : (V ⊓ U : Submodule 𝕜 H) = U ⊓ V := inf_comm V U
  have hbmem : V.starProjection x ∈ V ⊓ (U ⊓ V)ᗮ := by
    have hx' : x ∈ ((V ⊓ U)ᗮ : Submodule 𝕜 H) := by rw [hUV]; exact hx.2
    have hmem := starProjection_mem_genericPart hV x hx'
    rw [hUV] at hmem
    exact hmem
  have hab : ‖⟪x, V.starProjection x⟫_𝕜‖ ≤ c * ‖x‖ * ‖V.starProjection x‖ :=
    norm_inner_le_friedrichsCosine U V hx hbmem
  have hval : ‖⟪V.starProjection x, x⟫_𝕜‖ = ‖V.starProjection x‖ ^ (2 : ℕ) := by
    rw [inner_starProjection_self hV x, inner_self_eq_norm_sq_to_K, norm_pow,
      RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
  have hconj : ‖⟪V.starProjection x, x⟫_𝕜‖ = ‖⟪x, V.starProjection x⟫_𝕜‖ := by
    rw [← inner_conj_symm, RCLike.norm_conj]
  have hnormsq : ‖V.starProjection x‖ ^ (2 : ℕ) ≤ c * ‖x‖ * ‖V.starProjection x‖ := by
    rw [← hval, hconj]
    exact hab
  have hbnorm : ‖V.starProjection x‖ ≤ c * ‖x‖ := by
    rcases eq_or_lt_of_le (norm_nonneg (V.starProjection x)) with h0 | hpos
    · rw [← h0]; positivity
    · nlinarith
  rw [norm_sub_starProjection_sq hV x]
  nlinarith [norm_nonneg (V.starProjection x), norm_nonneg x]

include hU hV in
/-- **The Friedrichs constant is optimal.**  Whenever the generic part `U ⊖ W` is nontrivial,
transverse unit vectors realize the bound `1 − c_F` to any accuracy. -/
theorem exists_transverse_unit_pairPrecision_le
    (hne : (U ⊓ ((U ⊓ V)ᗮ : Submodule 𝕜 H)) ≠ ⊥) {ε : ℝ} (hε : 0 < ε) :
    haveI : CompleteSpace U := hU.completeSpace_coe
    haveI : CompleteSpace V := hV.completeSpace_coe
    ∃ x ∈ ((U ⊓ V)ᗮ : Submodule 𝕜 H), ‖x‖ = 1 ∧
      pairPrecision U V x ≤ 1 - friedrichsCosine U V + ε := by
  haveI : CompleteSpace U := hU.completeSpace_coe
  haveI : CompleteSpace V := hV.completeSpace_coe
  set c : ℝ := friedrichsCosine U V with hc
  have hcnn : 0 ≤ c := friedrichsCosine_nonneg U V
  obtain ⟨u0, hu0mem, hu0ne⟩ := (Submodule.ne_bot_iff _).mp hne
  have hu0n : (0 : ℝ) < ‖u0‖ := norm_pos_iff.mpr hu0ne
  set u : H := (‖u0‖ : 𝕜)⁻¹ • u0 with hu
  have humem : u ∈ U ⊓ ((U ⊓ V)ᗮ : Submodule 𝕜 H) := Submodule.smul_mem _ _ hu0mem
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg hu0n.le,
      inv_mul_cancel₀ hu0n.ne']
  rcases eq_or_lt_of_le hcnn with hc0 | hcpos
  · refine ⟨u, humem.2, hun, ?_⟩
    have hUu : U.starProjection u = u := U.starProjection_eq_self_iff.mpr humem.1
    rw [pairPrecision, hUu, sub_self, norm_zero, norm_sub_starProjection_sq hV u, hun, ← hc0]
    nlinarith [sq_nonneg ‖V.starProjection u‖, hε.le]
  · have hne' : (friedrichsCosineSet U V).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      rw [hc, friedrichsCosine, hempty, Real.sSup_empty] at hcpos
      exact lt_irrefl 0 hcpos
    obtain ⟨r, hrmem, hrlt⟩ :=
      exists_lt_of_lt_csSup hne' (show c - ε / 2 < c by linarith)
    obtain ⟨p, hpmem, q, hqmem, hpn, hqn, rfl⟩ := hrmem
    set t : ℝ := ‖⟪p, q⟫_𝕜‖ with ht
    have htnn : 0 ≤ t := norm_nonneg _
    have htlt : c - ε / 2 < t := hrlt
    obtain ⟨θ, hθ, hθval⟩ : ∃ θ : 𝕜, ‖θ‖ = 1 ∧ θ * ⟪p, q⟫_𝕜 = ((t : ℝ) : 𝕜) := by
      rcases eq_or_ne (⟪p, q⟫_𝕜) 0 with h0 | h0
      · exact ⟨1, norm_one, by rw [h0, mul_zero, ht, h0, norm_zero, RCLike.ofReal_zero]⟩
      · refine ⟨((t : ℝ) : 𝕜) * (⟪p, q⟫_𝕜)⁻¹, ?_, ?_⟩
        · rw [norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg htnn, ht,
            mul_inv_cancel₀ (norm_ne_zero_iff.mpr h0)]
        · field_simp
    set q' : H := θ • q with hq'
    have hq'mem : q' ∈ V ⊓ ((U ⊓ V)ᗮ : Submodule 𝕜 H) := Submodule.smul_mem _ _ hqmem
    have hq'n : ‖q'‖ = 1 := by rw [hq', norm_smul, hθ, hqn, one_mul]
    have hpq : ⟪p, q'⟫_𝕜 = ((t : ℝ) : 𝕜) := by rw [hq', inner_smul_right, hθval]
    have hqp : ⟪q', p⟫_𝕜 = ((t : ℝ) : 𝕜) := by
      rw [← inner_conj_symm, hpq, RCLike.conj_ofReal]
    set x0 : H := p + q' with hx0
    have hx0mem : x0 ∈ ((U ⊓ V)ᗮ : Submodule 𝕜 H) := Submodule.add_mem _ hpmem.2 hq'mem.2
    have hx0n : ‖x0‖ ^ (2 : ℕ) = 2 * (1 + t) := by
      rw [hx0, norm_add_sq (𝕜 := 𝕜) p q', hpn, hq'n, hpq, RCLike.ofReal_re]
      ring
    have hx0pos : (0 : ℝ) < ‖x0‖ := by
      have hsq : (0 : ℝ) < ‖x0‖ ^ (2 : ℕ) := by rw [hx0n]; nlinarith
      nlinarith [norm_nonneg x0]
    have hPU : 1 + t ≤ ‖U.starProjection x0‖ := by
      have hinner : ⟪x0, p⟫_𝕜 = ((1 + t : ℝ) : 𝕜) := by
        rw [hx0, inner_add_left, inner_self_eq_norm_sq_to_K, hpn, hqp]
        push_cast
        ring
      have hnorm := norm_starProjection_le_of_inner hU x0 hpmem.1 hpn
      rw [hinner, RCLike.norm_ofReal, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + t)] at hnorm
      exact hnorm
    have hPV : 1 + t ≤ ‖V.starProjection x0‖ := by
      have hinner : ⟪x0, q'⟫_𝕜 = ((1 + t : ℝ) : 𝕜) := by
        rw [hx0, inner_add_left, inner_self_eq_norm_sq_to_K, hq'n, hpq]
        push_cast
        ring
      have hnorm := norm_starProjection_le_of_inner hV x0 hq'mem.1 hq'n
      rw [hinner, RCLike.norm_ofReal, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + t)] at hnorm
      exact hnorm
    have hprec0 : pairPrecision U V x0 ≤ 2 * (1 + t) * (1 - t) := by
      rw [pairPrecision, norm_sub_starProjection_sq hU x0, norm_sub_starProjection_sq hV x0,
        hx0n]
      nlinarith [hPU, hPV, htnn]
    refine ⟨(‖x0‖ : 𝕜)⁻¹ • x0, Submodule.smul_mem _ _ hx0mem, ?_, ?_⟩
    · rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg hx0pos.le,
        inv_mul_cancel₀ hx0pos.ne']
    · rw [pairPrecision_smul hU hV, norm_inv, RCLike.norm_ofReal,
        abs_of_nonneg hx0pos.le, inv_pow, hx0n]
      have hprec : pairPrecision U V x0 ≤ 2 * (1 + t) * (1 - t) := hprec0
      have hden : (0 : ℝ) < 2 * (1 + t) := by nlinarith
      rw [inv_mul_le_iff₀ hden]
      nlinarith [hε.le]

end Closed

end GaloisForLFunctions.HTGeometry
