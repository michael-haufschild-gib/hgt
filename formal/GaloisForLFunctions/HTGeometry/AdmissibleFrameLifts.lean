import GaloisForLFunctions.HTGeometry.DeterminantLineConnection

/-!
# Admissible frames on the restricted Grassmannian and their smooth local lifts

Relative to a polarization projection `Q`, a frame of an orthogonal projection `P` is an operator
`w` with `w Q = w`, invertible Gram operator `Ĝ = w† w + (1 − Q)` and `w Ĝ⁻¹ w† = P`; it is
*admissible* when `w − Q` is Hilbert–Schmidt and `Q w − Q` has finite rank.

* `isFrameOf_of_inverse`: a two-sided inverse `L` between `ran Q` and `ran P` makes `w` a frame,
  with `Ĝ⁻¹ = L L† + (1 − Q)`.
* `isFrameOf_transfer`: from a frame `u₀` of `P₀`, `P u₀ (1 + E)⁻¹` is a frame of every nearby `P`.
* `exists_basisProj_approx`, `exists_finiteRank_unit`: Hilbert–Schmidt operators are norm limits
  of finite-rank ones, hence `1 + (finite rank) + (Hilbert–Schmidt)` becomes invertible after a
  finite-rank correction (index zero).
* `exists_admissibleFrame_of_near`, `exists_admissibleFrame_of_isPreconnected`: admissible frames
  propagate across distance `< 1`, so the admissible sector is clopen.
* `liftY_isFrameOf`, `contDiffAt_liftY`: the smooth local lift `(P₀ + D) u₀ (1 + Q D u₀)⁻¹`, with
  `ran Q`-defect `(Q u₀ − Q)(1 + Q D u₀)⁻¹` in the fixed finite-dimensional range of `Q u₀ − Q`.
-/

set_option autoImplicit false

open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Frames -/

section Frames

variable {Q w P L : H →L[ℂ] H}

/-- `w` is a frame of the orthogonal projection `P` relative to `Q`. -/
def IsFrameOf (Q w P : H →L[ℂ] H) : Prop :=
  w * Q = w ∧ IsUnit (frameGram Q w) ∧ frameProj w (Ring.inverse (frameGram Q w)) = P

/-- **Frame criterion.**  If `w Q = w` and `L` is a two-sided inverse of `w` between `ran Q` and
`ran P` (`L w = Q`, `w L = P`, `Q L = L`), then `Ĝ⁻¹ = L L† + (1 − Q)` and `w` is a frame of `P`. -/
theorem isFrameOf_of_inverse (hQ : IsSelfAdjoint Q) (hQi : IsIdempotentElem Q)
    (hP : IsSelfAdjoint P) (hPi : IsIdempotentElem P) (hwQ : w * Q = w) (hLw : L * w = Q)
    (hwL : w * L = P) (hQL : Q * L = L) : IsFrameOf Q w P := by
  have hPw : P * w = w := by rw [← hwL, mul_assoc, hLw, hwQ]
  have hLadj : adjoint L * adjoint w = P := by
    rw [← star_eq_adjoint, ← star_eq_adjoint, ← star_mul, hwL, hP.star_eq]
  have hwadjL : adjoint w * adjoint L = Q := by
    rw [← star_eq_adjoint, ← star_eq_adjoint, ← star_mul, hLw, hQ.star_eq]
  have hadjPw : adjoint w * P = adjoint w := by
    rw [← star_eq_adjoint, ← hP.star_eq, ← star_mul, hPw]
  have hwc : w * (1 - Q) = 0 := by rw [mul_sub, mul_one, hwQ, sub_self]
  have hcL : (1 - Q) * L = 0 := by rw [sub_mul, one_mul, hQL, sub_self]
  have hLc : adjoint L * (1 - Q) = 0 := by
    have := congrArg star hcL
    rw [star_mul, star_sub, star_one, hQ.star_eq, star_zero, star_eq_adjoint] at this
    exact this
  have hcw : (1 - Q) * adjoint w = 0 := by
    have := congrArg star hwc
    rw [star_mul, star_sub, star_one, hQ.star_eq, star_zero, star_eq_adjoint] at this
    exact this
  set Ginv := L * adjoint L + (1 - Q)
  have h1 : frameGram Q w * Ginv = 1 := by
    unfold frameGram
    calc (adjoint w * w + (1 - Q)) * (L * adjoint L + (1 - Q))
        = adjoint w * (w * L) * adjoint L + adjoint w * (w * (1 - Q)) +
            (1 - Q) * L * adjoint L + (1 - Q) * (1 - Q) := by noncomm_ring
      _ = 1 := by
          rw [hwL, hadjPw, hwadjL, hwc, hcL, sub_mul, one_mul, mul_sub, mul_one, hQi.eq]
          noncomm_ring
  have h2 : Ginv * frameGram Q w = 1 := by
    unfold frameGram
    calc (L * adjoint L + (1 - Q)) * (adjoint w * w + (1 - Q))
        = L * (adjoint L * adjoint w) * w + L * (adjoint L * (1 - Q)) +
            (1 - Q) * adjoint w * w + (1 - Q) * (1 - Q) := by noncomm_ring
      _ = 1 := by
          rw [hLadj, hLc, hcw, mul_assoc L P w, hPw, hLw, sub_mul, one_mul, mul_sub, mul_one,
            hQi.eq]
          noncomm_ring
  have hunit : IsUnit (frameGram Q w) := ⟨⟨_, Ginv, h1, h2⟩, rfl⟩
  have hinv : Ring.inverse (frameGram Q w) = Ginv := by
    rw [show frameGram Q w = ((⟨_, Ginv, h1, h2⟩ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) from rfl,
      Ring.inverse_unit]
    rfl
  refine ⟨hwQ, hunit, ?_⟩
  rw [hinv]
  unfold frameProj
  calc w * (L * adjoint L + (1 - Q)) * adjoint w
      = (w * L) * (adjoint L * adjoint w) + w * (1 - Q) * adjoint w := by noncomm_ring
    _ = P := by rw [hwL, hLadj, hwc, zero_mul, add_zero, hPi.eq]

/-- **Transfer of frames.**  Let `u₀` be a frame of `P₀`, `P` an orthogonal projection, and `E` an
operator supported in `ran Q` (`Q E = E = E Q`) with `1 + E`, `T = 1 + P(P₀ − P)P` and
`T₀ = 1 + P₀(P − P₀)P₀` invertible.  Then `w = P u₀ (1 + E)⁻¹` is a frame of `P`, with
`Q w − Q = (Q P u₀ − Q − E)(1 + E)⁻¹`. -/
theorem isFrameOf_transfer (hQ : IsSelfAdjoint Q) (hQi : IsIdempotentElem Q)
    {u₀ P₀ E : H →L[ℂ] H} (hu₀ : IsFrameOf Q u₀ P₀) (hP : IsSelfAdjoint P)
    (hPi : IsIdempotentElem P) (hQE : Q * E = E) (hEQ : E * Q = E) (hE : IsUnit (1 + E))
    (hT : IsUnit (1 + P * (P₀ - P) * P)) (hT₀ : IsUnit (1 + P₀ * (P - P₀) * P₀)) :
    IsFrameOf Q (P * u₀ * Ring.inverse (1 + E)) P ∧
      Q * (P * u₀ * Ring.inverse (1 + E)) - Q = (Q * P * u₀ - Q - E) * Ring.inverse (1 + E) := by
  obtain ⟨hu₀Q, hG₀, hP₀⟩ := hu₀
  set A₀ := Ring.inverse (frameGram Q u₀)
  have hA₀ : A₀ * frameGram Q u₀ = 1 := Ring.inverse_mul_cancel _ hG₀
  have hA₀' : frameGram Q u₀ * A₀ = 1 := Ring.mul_inverse_cancel _ hG₀
  have hAu : A₀ * adjoint u₀ * u₀ = Q := frameInv_adjoint_mul hQi hu₀Q hA₀
  have hPu : P₀ * u₀ = u₀ := by rw [← hP₀]; exact frameProj_mul_frame hQi hu₀Q hA₀
  have hQA : Q * A₀ = A₀ * Q := frameInv_comm hQ hQi hu₀Q hA₀ hA₀'
  have hQu : Q * adjoint u₀ = adjoint u₀ := adjoint_mul_of_mul_eq hQ hu₀Q
  have hP₀i : IsIdempotentElem P₀ := by
    rw [← hP₀]; unfold IsIdempotentElem frameProj
    calc u₀ * A₀ * adjoint u₀ * (u₀ * A₀ * adjoint u₀) = u₀ * (A₀ * adjoint u₀ * u₀) * A₀ *
        adjoint u₀ := by noncomm_ring
      _ = u₀ * A₀ * adjoint u₀ := by rw [hAu, hu₀Q]
  set B := Ring.inverse (1 + E)
  have hB : B * (1 + E) = 1 := Ring.inverse_mul_cancel _ hE
  have hB' : (1 + E) * B = 1 := Ring.mul_inverse_cancel _ hE
  have hcomm : Q * (1 + E) = (1 + E) * Q := by rw [mul_add, add_mul, hQE, hEQ, mul_one, one_mul]
  have hBQ : B * Q = Q * B := by
    calc B * Q = B * Q * ((1 + E) * B) := by rw [hB', mul_one]
      _ = B * (Q * (1 + E)) * B := by noncomm_ring
      _ = B * ((1 + E) * Q) * B := by rw [hcomm]
      _ = (B * (1 + E)) * Q * B := by noncomm_ring
      _ = Q * B := by rw [hB, one_mul]
  set T := 1 + P * (P₀ - P) * P
  set T₀ := 1 + P₀ * (P - P₀) * P₀
  have hTi : Ring.inverse T * T = 1 := Ring.inverse_mul_cancel _ hT
  have hTi' : T * Ring.inverse T = 1 := Ring.mul_inverse_cancel _ hT
  have hT₀i : Ring.inverse T₀ * T₀ = 1 := Ring.inverse_mul_cancel _ hT₀
  have hPT : P * T = P * P₀ * P := by
    calc P * T = P + (P * P) * P₀ * P - (P * P) * (P * P) := by simp only [T]; noncomm_ring
      _ = P * P₀ * P := by rw [hPi.eq, hPi.eq]; noncomm_ring
  have hP₀T₀ : P₀ * P * P₀ = T₀ * P₀ := by
    symm
    calc T₀ * P₀ = P₀ + P₀ * P * (P₀ * P₀) - (P₀ * P₀) * (P₀ * P₀) := by
          simp only [T₀]; noncomm_ring
      _ = P₀ * P * P₀ := by rw [hP₀i.eq, hP₀i.eq]; noncomm_ring
  set w := P * u₀ * B
  -- the inverse pair
  set X' := A₀ * adjoint u₀ * P * Ring.inverse T
  have hPuX : P * u₀ * X' = P := by
    calc P * u₀ * X' = P * (u₀ * A₀ * adjoint u₀) * P * Ring.inverse T := by
          simp only [X']; noncomm_ring
      _ = P * T * Ring.inverse T := by
          rw [show u₀ * A₀ * adjoint u₀ = P₀ from hP₀, ← hPT]
      _ = P := by rw [mul_assoc, hTi', mul_one]
  set L₁ := (1 + E) * A₀ * adjoint u₀ * Ring.inverse T₀ * P₀
  have hL₁w : L₁ * w = Q := by
    have h0 : P₀ * P * u₀ = P₀ * P * P₀ * u₀ := by rw [mul_assoc (P₀ * P) P₀ u₀, hPu]
    have h1 : Ring.inverse T₀ * P₀ * P * u₀ = u₀ := by
      calc Ring.inverse T₀ * P₀ * P * u₀ = Ring.inverse T₀ * (P₀ * P * u₀) := by noncomm_ring
        _ = Ring.inverse T₀ * (T₀ * P₀ * u₀) := by rw [h0, hP₀T₀]
        _ = u₀ := by rw [← mul_assoc, ← mul_assoc, hT₀i, one_mul, hPu]
    calc L₁ * w = (1 + E) * A₀ * adjoint u₀ * (Ring.inverse T₀ * P₀ * P * u₀) * B := by
          simp only [L₁, w]; noncomm_ring
      _ = (1 + E) * (A₀ * adjoint u₀ * u₀) * B := by rw [h1]; noncomm_ring
      _ = Q := by
          rw [hAu, ← hcomm, mul_assoc, hB', mul_one]
  have hPw : P * w = w := by simp only [w, ← mul_assoc, hPi.eq]
  have hwX : w * ((1 + E) * X') = P := by
    calc w * ((1 + E) * X') = P * u₀ * (B * (1 + E)) * X' := by simp only [w]; noncomm_ring
      _ = P := by rw [hB, mul_one, hPuX]
  have hwQ : w * Q = w := by
    simp only [w]; rw [mul_assoc, hBQ, ← mul_assoc, mul_assoc P u₀ Q, hu₀Q]
  set L := L₁ * P
  have hLw : L * w = Q := by simp only [L]; rw [mul_assoc, hPw, hL₁w]
  have hwL : w * L = P := by
    calc w * L = w * L₁ * (w * ((1 + E) * X')) := by simp only [L]; rw [hwX]; noncomm_ring
      _ = w * (L₁ * w) * ((1 + E) * X') := by noncomm_ring
      _ = P := by rw [hL₁w, hwQ, hwX]
  have hQL : Q * L = L := by
    simp only [L, L₁]
    calc Q * ((1 + E) * A₀ * adjoint u₀ * Ring.inverse T₀ * P₀ * P)
        = (Q * (1 + E)) * A₀ * adjoint u₀ * Ring.inverse T₀ * P₀ * P := by noncomm_ring
      _ = (1 + E) * (Q * A₀) * adjoint u₀ * Ring.inverse T₀ * P₀ * P := by
          rw [hcomm]; noncomm_ring
      _ = (1 + E) * A₀ * (Q * adjoint u₀) * Ring.inverse T₀ * P₀ * P := by rw [hQA]; noncomm_ring
      _ = (1 + E) * A₀ * adjoint u₀ * Ring.inverse T₀ * P₀ * P := by rw [hQu]
  refine ⟨isFrameOf_of_inverse hQ hQi hP hPi hwQ hLw hwL hQL, ?_⟩
  -- the `Q`-defect
  calc Q * (P * u₀ * B) - Q = (Q * P * u₀ - Q - E) * B + ((Q * (1 + E)) * B - Q) := by
        rw [mul_add, mul_one, hQE]; noncomm_ring
    _ = (Q * P * u₀ - Q - E) * B := by rw [mul_assoc Q (1 + E) B, hB', mul_one, sub_self, add_zero]

end Frames


/-! ## Invertibility criteria -/

section Units

theorem isUnit_one_add_of_norm_lt {X : H →L[ℂ] H} (h : ‖X‖ < 1) : IsUnit (1 + X) := by
  refine ⟨Units.oneSub (-X) (by rwa [norm_neg]), ?_⟩
  show 1 - -X = 1 + X
  rw [sub_neg_eq_add]

/-- For orthogonal projections at distance `< 1`, the comparison operators
`1 + P(P₀ − P)P` and `1 + P₀(P − P₀)P₀` are invertible. -/
theorem isUnit_compression_of_norm_lt {P P₀ : H →L[ℂ] H} (hP : IsStarProjection P)
    (hP₀ : IsStarProjection P₀) (h : ‖P - P₀‖ < 1) :
    IsUnit (1 + P * (P₀ - P) * P) ∧ IsUnit (1 + P₀ * (P - P₀) * P₀) := by
  have n1 := IsStarProjection.norm_le P hP
  have n0 := IsStarProjection.norm_le P₀ hP₀
  constructor
  · refine isUnit_one_add_of_norm_lt ?_
    calc ‖P * (P₀ - P) * P‖ ≤ ‖P‖ * ‖P₀ - P‖ * ‖P‖ := by
          refine (norm_mul_le _ _).trans ?_
          gcongr
          exact norm_mul_le _ _
      _ ≤ 1 * ‖P - P₀‖ * 1 := by rw [norm_sub_rev]; gcongr
      _ < 1 := by simpa using h
  · refine isUnit_one_add_of_norm_lt ?_
    calc ‖P₀ * (P - P₀) * P₀‖ ≤ ‖P₀‖ * ‖P - P₀‖ * ‖P₀‖ := by
          refine (norm_mul_le _ _).trans ?_
          gcongr
          exact norm_mul_le _ _
      _ ≤ 1 * ‖P - P₀‖ * 1 := by gcongr
      _ < 1 := by simpa using h

omit [CompleteSpace H] in
/-- **Finite-rank perturbations of the identity**: if `G` has range in a finite-dimensional `V`
and `1 + G` is injective, then `1 + G` is invertible. -/
theorem isUnit_one_add_of_range_le {G : H →L[ℂ] H} {V : Submodule ℂ H} [FiniteDimensional ℂ V]
    (hG : ∀ x, G x ∈ V) (hinj : Function.Injective ⇑(1 + G)) : IsUnit (1 + G) := by
  have hmaps : ∀ v ∈ V, (1 + G) v ∈ V := fun v hv => by
    simpa using V.add_mem hv (hG v)
  set e : V →ₗ[ℂ] V := ((1 + G : H →L[ℂ] H) : H →ₗ[ℂ] H).restrict hmaps
  have he : Function.Injective e := fun x y hxy => Subtype.ext (hinj (congrArg Subtype.val hxy))
  set eq : V ≃ₗ[ℂ] V := LinearEquiv.ofBijective e ⟨he, LinearMap.injective_iff_surjective.mp he⟩
  set Gc : H →L[ℂ] V := G.codRestrict V hG
  set einv : V →L[ℂ] V := LinearMap.toContinuousLinearMap (eq.symm : V →ₗ[ℂ] V)
  set h : H →L[ℂ] H := 1 - V.subtypeL.comp (einv.comp Gc)
  have he_apply : ∀ v : V, ((e v : V) : H) = v + G v := fun v => by simp [e]
  have hy : ∀ x, ((einv (Gc x) : V) : H) + G (einv (Gc x)) = G x := fun x => by
    rw [← he_apply]
    show ((e (eq.symm (Gc x)) : V) : H) = G x
    rw [show e (eq.symm (Gc x)) = eq (eq.symm (Gc x)) from rfl, LinearEquiv.apply_symm_apply]
    rfl
  have h1 : (1 + G) * h = 1 := by
    ext x
    simp only [h, mul_apply_eq_comp, comp_apply, add_apply, sub_apply, one_apply_eq_self,
      Submodule.subtypeL_apply, map_sub]
    have := hy x
    simp only [einv, Gc] at this ⊢
    rw [← this]
    abel
  have h2 : h * (1 + G) = 1 := by
    ext x
    have hGx : einv (Gc ((1 + G) x)) = Gc x := by
      apply eq.injective
      show e (eq.symm (Gc ((1 + G) x))) = e (Gc x)
      rw [show e (eq.symm (Gc ((1 + G) x))) = eq (eq.symm (Gc ((1 + G) x))) from rfl,
        LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [he_apply]
      simp [Gc]
    simp only [h, mul_apply_eq_comp, comp_apply, sub_apply, one_apply_eq_self,
      Submodule.subtypeL_apply, hGx]
    simp [Gc]
  exact ⟨⟨1 + G, h, h1, h2⟩, rfl⟩

end Units


/-! ## Finite-rank approximation of Hilbert–Schmidt operators -/

section Approximation

open scoped InnerProductSpace

/-- The span of finitely many vectors of the canonical basis. -/
def basisSpan (s : Finset ((exists_hilbertBasis ℂ H).choose)) : Submodule ℂ H :=
  Submodule.span ℂ (Set.range fun i : s => hsBasis ℂ H i)

instance (s : Finset ((exists_hilbertBasis ℂ H).choose)) : FiniteDimensional ℂ (basisSpan s) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

/-- The orthogonal projection onto the span of finitely many vectors of the canonical basis. -/
def basisProj (s : Finset ((exists_hilbertBasis ℂ H).choose)) : H →L[ℂ] H :=
  (basisSpan s).starProjection

theorem basisProj_apply_basis (s : Finset ((exists_hilbertBasis ℂ H).choose))
    (i : (exists_hilbertBasis ℂ H).choose) [Decidable (i ∈ s)] :
    basisProj s (hsBasis ℂ H i) = if i ∈ s then hsBasis ℂ H i else 0 := by
  unfold basisProj
  split_ifs with hi
  · exact Submodule.starProjection_eq_self_iff.mpr (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
  · have hperp : hsBasis ℂ H i ∈ (basisSpan s)ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      unfold basisSpan at hu
      refine Submodule.span_induction (fun x hx => ?_) (by simp)
        (fun x y _ _ hx hy => by rw [inner_add_right, hx, hy, add_zero])
        (fun c x _ hx => by rw [inner_smul_right, hx, mul_zero]) hu
      obtain ⟨⟨j, hj⟩, rfl⟩ := hx
      have hne : i ≠ j := fun h => hi (h ▸ hj)
      exact (hsBasis ℂ H).orthonormal.2 hne
    show (((basisSpan s).orthogonalProjectionOnto (hsBasis ℂ H i) : basisSpan s) : H) = 0
    rw [Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hperp]
    rfl

/-- **Hilbert–Schmidt operators are norm limits of finite-rank operators**: for every `ε > 0` some
finite basis projection `P_s` has `‖K − K P_s‖ < ε`. -/
theorem exists_basisProj_approx {K : H →L[ℂ] H} (hK : IsHilbertSchmidt K) {ε : ℝ} (hε : 0 < ε) :
    ∃ s, ‖K - K * basisProj s‖ < ε := by
  classical
  set f := fun i => ‖K (hsBasis ℂ H i)‖ ^ 2
  have hsum : Summable f := hK.summable (hsBasis ℂ H)
  obtain ⟨s, hs⟩ := ((tendsto_order.1 (tendsto_tsum_compl_atTop_zero f)).2 (ε ^ 2)
    (by positivity)).exists
  refine ⟨s, ?_⟩
  have hKs : IsHilbertSchmidt (K - K * basisProj s) := hK.sub (hK.comp_right _)
  have happ : ∀ i, (K - K * basisProj s) (hsBasis ℂ H i) =
      if i ∈ s then 0 else K (hsBasis ℂ H i) := fun i => by
    rw [sub_apply, mul_apply_eq_comp, basisProj_apply_basis]
    split_ifs <;> simp
  have hsq : hsNormSq (K - K * basisProj s) = ∑' b : {x // x ∉ s}, f b := by
    rw [hsNormSq, show (∑' b : {x // x ∉ s}, f b) = ∑' b : ({x | x ∉ s} : Set _), f b from rfl,
      tsum_subtype ({x | x ∉ s} : Set _) f]
    congr 1
    funext i
    rw [happ]
    by_cases hi : i ∈ s <;> simp [hi, Set.indicator, f]
  calc ‖K - K * basisProj s‖ ≤ hsNorm (K - K * basisProj s) := norm_le_hsNorm hKs
    _ = Real.sqrt (∑' b : {x // x ∉ s}, f b) := by rw [hsNorm, hsq]
    _ < Real.sqrt (ε ^ 2) := Real.sqrt_lt_sqrt (tsum_nonneg fun _ => by positivity) hs
    _ = ε := Real.sqrt_sq hε.le

end Approximation


/-! ## Index zero: finite-rank corrections -/

section IndexZero

variable {Q : H →L[ℂ] H}

/-- **Index zero for compact perturbations supported in `ran Q`.**  If `R` has finite rank and `K`
is Hilbert–Schmidt, both supported in `ran Q`, then some finite-rank `F` supported in `ran Q` makes
`1 + R + K + F` invertible. -/
theorem exists_finiteRank_unit (hQ : IsStarProjection Q) {R K : H →L[ℂ] H} {V : Submodule ℂ H}
    [FiniteDimensional ℂ V] (hR : ∀ x, R x ∈ V) (hQR : Q * R = R) (hRQ : R * Q = R)
    (hK : IsHilbertSchmidt K) (hQK : Q * K = K) (hKQ : K * Q = K) :
    ∃ (F : H →L[ℂ] H) (W : Submodule ℂ H), FiniteDimensional ℂ W ∧ (∀ x, F x ∈ W) ∧
      Q * F = F ∧ F * Q = F ∧ IsUnit (1 + (R + K + F)) := by
  classical
  have hQn := IsStarProjection.norm_le Q hQ
  have hQi := hQ.isIdempotentElem
  obtain ⟨s, hs⟩ := exists_basisProj_approx hK one_pos
  set Kn := K * basisProj s * Q
  have hKKn : K - Kn = (K - K * basisProj s) * Q := by
    simp only [Kn, sub_mul, hKQ]
  have hnorm : ‖K - Kn‖ < 1 := by
    rw [hKKn]
    calc ‖(K - K * basisProj s) * Q‖ ≤ ‖K - K * basisProj s‖ * ‖Q‖ := norm_mul_le _ _
      _ ≤ ‖K - K * basisProj s‖ * 1 := by gcongr
      _ < 1 := by simpa using hs
  set U := 1 + (K - Kn)
  have hU : IsUnit U := isUnit_one_add_of_norm_lt hnorm
  have hQKn : Q * Kn = Kn := by simp only [Kn, ← mul_assoc, hQK]
  have hKnQ : Kn * Q = Kn := by simp only [Kn, mul_assoc, hQi.eq]
  have hUQ : U * Q = Q * U := by
    simp only [U, add_mul, mul_add, one_mul, mul_one, sub_mul, mul_sub, hKQ, hQK, hKnQ, hQKn]
  set Ui := Ring.inverse U
  have hUi : Ui * U = 1 := Ring.inverse_mul_cancel _ hU
  have hUi' : U * Ui = 1 := Ring.mul_inverse_cancel _ hU
  have hUiQ : Ui * Q = Q * Ui := by
    calc Ui * Q = Ui * Q * (U * Ui) := by rw [hUi', mul_one]
      _ = Ui * (Q * U) * Ui := by noncomm_ring
      _ = Ui * (U * Q) * Ui := by rw [hUQ]
      _ = (Ui * U) * Q * Ui := by noncomm_ring
      _ = Q * Ui := by rw [hUi, one_mul]
  set G := Ui * (R + Kn)
  -- the range of `G` is finite-dimensional
  set W₀ : Submodule ℂ H := V ⊔ (basisSpan s).map (K : H →ₗ[ℂ] H)
  haveI : FiniteDimensional ℂ W₀ := Submodule.finiteDimensional_sup _ _
  have hW₀ : ∀ x, (R + Kn) x ∈ W₀ := fun x => by
    refine W₀.add_mem (Submodule.mem_sup_left (hR x)) (Submodule.mem_sup_right ?_)
    exact ⟨basisProj s (Q x), Submodule.starProjection_apply_mem _ _, rfl⟩
  set Vs := LinearMap.range (G : H →ₗ[ℂ] H)
  have hVsle : Vs ≤ W₀.map (Ui : H →ₗ[ℂ] H) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(R + Kn) x, hW₀ x, rfl⟩
  haveI : FiniteDimensional ℂ Vs := Submodule.finiteDimensional_of_le hVsle
  have hQG : Q * G = G := by
    calc Q * G = (Q * Ui) * (R + Kn) := by simp only [G]; noncomm_ring
      _ = Ui * (Q * R + Q * Kn) := by rw [← hUiQ]; noncomm_ring
      _ = G := by rw [hQR, hQKn]
  have hGQ : G * Q = G := by simp only [G, mul_assoc, add_mul, hRQ, hKnQ]
  set Ps := Vs.starProjection
  have hQPs : Q * Ps = Ps := by
    ext x
    obtain ⟨y, hy⟩ := Submodule.starProjection_apply_mem Vs x
    show Q (Ps x) = Ps x
    rw [show Ps x = G y from hy.symm]
    show (Q * G) y = G y
    rw [hQG]
  have hPsQ : Ps * Q = Ps := by
    have h1 : IsSelfAdjoint Ps := isSelfAdjoint_starProjection Vs
    have := congrArg star hQPs
    rwa [star_mul, h1.star_eq, hQ.isSelfAdjoint.star_eq] at this
  set c : ℂ := ((‖G‖ + 1 : ℝ) : ℂ)
  set G' := G + c • Ps
  have hG'V : ∀ x, G' x ∈ Vs := fun x => by
    refine Vs.add_mem ⟨x, rfl⟩ (Vs.smul_mem c (Submodule.starProjection_apply_mem Vs x))
  have hinj : Function.Injective ⇑(1 + G') := by
    intro x y hxy
    set z := x - y
    have hz0 : z + G' z = 0 := by
      have : (1 + G') z = 0 := by simp only [z, map_sub, hxy, sub_self]
      simpa using this
    have hzV : z ∈ Vs := by
      have : z = -(G' z) := eq_neg_of_add_eq_zero_left hz0
      rw [this]; exact Vs.neg_mem (hG'V z)
    have hPz : Ps z = z := Submodule.starProjection_eq_self_iff.mpr hzV
    have hlin : (1 + c) • z = -(G z) := by
      have : z + (G z + c • z) = 0 := by simpa [G', hPz] using hz0
      rw [add_smul, one_smul]
      linear_combination (norm := module) this
    have hn : (‖G‖ + 2) * ‖z‖ ≤ ‖G‖ * ‖z‖ := by
      have h1 : ‖(1 + c) • z‖ = (‖G‖ + 2) * ‖z‖ := by
        rw [norm_smul]
        congr 1
        simp only [c]
        rw [show (1 : ℂ) + ((‖G‖ + 1 : ℝ) : ℂ) = ((‖G‖ + 2 : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [← h1, hlin, norm_neg]
      exact le_opNorm G z
    have : ‖z‖ ≤ 0 := by nlinarith [norm_nonneg z, norm_nonneg G]
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hG'unit : IsUnit (1 + G') := isUnit_one_add_of_range_le hG'V hinj
  set F := U * (c • Ps)
  have hfac : 1 + (R + K + F) = U * (1 + G') := by
    have : U * G = R + Kn := by simp only [G, ← mul_assoc, hUi', one_mul]
    calc 1 + (R + K + F) = 1 + (K - Kn) + (R + Kn) + U * (c • Ps) := by simp only [F]; abel
      _ = U * (1 + G') := by rw [← this]; simp only [G', U]; noncomm_ring
  refine ⟨F, Vs.map (U : H →ₗ[ℂ] H), inferInstance, fun x => ⟨c • Ps x, Vs.smul_mem c
    (Submodule.starProjection_apply_mem Vs x), by simp [F]⟩, ?_, ?_, ?_⟩
  · simp only [F]; rw [← mul_assoc, ← hUQ, mul_assoc, mul_smul_comm, hQPs]
  · simp only [F]; rw [mul_assoc, smul_mul_assoc, hPsQ]
  · rw [hfac]; exact hU.mul hG'unit

end IndexZero


/-! ## Admissible frames and their propagation -/

section Admissible

variable {Q : H →L[ℂ] H}

/-- An admissible frame of `P` relative to `Q`: a frame `u` with `u − Q` Hilbert–Schmidt whose
`ran Q`-defect `Q u − Q` has finite rank. -/
def IsAdmissibleFrame (Q u P : H →L[ℂ] H) : Prop :=
  IsFrameOf Q u P ∧ IsHilbertSchmidt (u - Q) ∧
    ∃ V : Submodule ℂ H, FiniteDimensional ℂ V ∧ ∀ x, (Q * u - Q) x ∈ V

/-- **Propagation of admissible frames**: an admissible frame of `P'` produces one of every
orthogonal projection `P` with `P − P'` Hilbert–Schmidt and `‖P − P'‖ < 1`. -/
theorem exists_admissibleFrame_of_near (hQ : IsStarProjection Q) {u' P' P : H →L[ℂ] H}
    (hu' : IsAdmissibleFrame Q u' P') (hP' : IsStarProjection P') (hP : IsStarProjection P)
    (hPP : IsHilbertSchmidt (P - P')) (hnear : ‖P - P'‖ < 1) :
    ∃ u, IsAdmissibleFrame Q u P := by
  obtain ⟨hframe, hY', V', hV'fin, hV'⟩ := hu'
  haveI := hV'fin
  have hQi := hQ.isIdempotentElem
  have hu'Q : u' * Q = u' := hframe.1
  have hPu' : P' * u' = u' := by
    rw [← hframe.2.2]
    exact frameProj_mul_frame hQi hu'Q (Ring.inverse_mul_cancel _ hframe.2.1)
  set R := Q * u' - Q
  set K := Q * (P - P') * u'
  have hQR : Q * R = R := by simp only [R, mul_sub, ← mul_assoc, hQi.eq]
  have hRQ : R * Q = R := by simp only [R, sub_mul, mul_assoc, hu'Q, hQi.eq]
  have hKhs : IsHilbertSchmidt K := (hPP.comp_left Q).comp_right u'
  have hQK : Q * K = K := by simp only [K, ← mul_assoc, hQi.eq]
  have hKQ : K * Q = K := by simp only [K, mul_assoc, hu'Q]
  obtain ⟨F, W, hWfin, hFW, hQF, hFQ, hunit⟩ :=
    exists_finiteRank_unit hQ (fun x => hV' x) hQR hRQ hKhs hQK hKQ
  haveI := hWfin
  set E := R + K + F
  have hQE : Q * E = E := by simp only [E, mul_add, hQR, hQK, hQF]
  have hEQ : E * Q = E := by simp only [E, add_mul, hRQ, hKQ, hFQ]
  obtain ⟨hT, hT₀⟩ := isUnit_compression_of_norm_lt hP hP' hnear
  obtain ⟨hfr, hdef⟩ := isFrameOf_transfer hQ.isSelfAdjoint hQi hframe hP.isSelfAdjoint
    hP.isIdempotentElem hQE hEQ hunit hT hT₀
  set B := Ring.inverse (1 + E)
  have hB' : (1 + E) * B = 1 := Ring.mul_inverse_cancel _ hunit
  refine ⟨P * u' * B, hfr, ?_, W, hWfin, fun x => ?_⟩
  · -- `u − Q = (P − P') u' B + (u' − Q) B − E B`
    have hEhs : IsHilbertSchmidt E := by
      have hEeq : E = Q * (u' - Q) + K + F := by
        simp only [E, R]; rw [mul_sub, hQi.eq]
      rw [hEeq]
      exact ((hY'.comp_left Q).add hKhs).add (isHilbertSchmidt_of_range_le hFW)
    have hid : P * u' * B - Q = (P - P') * u' * B + (u' - Q) * B - E * B := by
      have hB1 : B - 1 = -(E * B) := by
        have : B + E * B = 1 := by rw [← hB']; noncomm_ring
        rw [← this]; abel
      have hQB : Q * B - Q = -(E * B) := by
        calc Q * B - Q = Q * (B - 1) := by noncomm_ring
          _ = -(Q * E * B) := by rw [hB1]; noncomm_ring
          _ = -(E * B) := by rw [hQE]
      calc P * u' * B - Q = (P - P') * u' * B + P' * u' * B - Q := by noncomm_ring
        _ = (P - P') * u' * B + (u' - Q) * B + (Q * B - Q) := by rw [hPu']; noncomm_ring
        _ = (P - P') * u' * B + (u' - Q) * B - E * B := by rw [hQB]; abel
    rw [hid]
    exact (((hPP.comp_right u').comp_right B).add (hY'.comp_right B)).sub (hEhs.comp_right B)
  · -- `Q u − Q = −F B` has range in `W`
    have hval : (Q * (P * u' * B) - Q) x = -(F (B x)) := by
      rw [hdef]
      have : Q * P * u' - Q - E = -F := by
        simp only [E, R, K, mul_sub, sub_mul]
        rw [mul_assoc Q P' u', hPu']; abel
      rw [this]; simp
    rw [hval]; exact W.neg_mem (hFW _)

/-- **The admissible sector is clopen**: along a preconnected family of orthogonal projections,
continuous in operator norm with pairwise Hilbert–Schmidt differences, one admissible frame
yields an admissible frame at every point. -/
theorem exists_admissibleFrame_of_isPreconnected (hQ : IsStarProjection Q) {X : Type*}
    [TopologicalSpace X] {S : Set X} (hS : IsPreconnected S) {P : X → H →L[ℂ] H}
    (hPc : ContinuousOn P S) (hproj : ∀ x ∈ S, IsStarProjection (P x))
    (hHS : ∀ x ∈ S, ∀ y ∈ S, IsHilbertSchmidt (P x - P y)) {x₀ x : X} (hx₀ : x₀ ∈ S)
    (hx : x ∈ S) (h₀ : ∃ u, IsAdmissibleFrame Q u (P x₀)) :
    ∃ u, IsAdmissibleFrame Q u (P x) := by
  refine hS.induction₂' (fun a b => (∃ u, IsAdmissibleFrame Q u (P a)) →
    ∃ u, IsAdmissibleFrame Q u (P b)) (fun a ha => ?_) (fun a b c _ _ _ hab hbc h => hbc (hab h))
    hx₀ hx h₀
  have hball : ∀ᶠ b in nhdsWithin a S, ‖P b - P a‖ < 1 := by
    have := (hPc a ha).tendsto
    have h1 : Metric.ball (P a) 1 ∈ nhds (P a) := Metric.ball_mem_nhds _ one_pos
    filter_upwards [this h1] with b hb
    simpa [dist_eq_norm] using hb
  filter_upwards [hball, self_mem_nhdsWithin] with b hb hbS
  refine ⟨fun ⟨u, hu⟩ => ?_, fun ⟨u, hu⟩ => ?_⟩
  · exact exists_admissibleFrame_of_near hQ hu (hproj a ha) (hproj b hbS) (hHS b hbS a ha) hb
  · exact exists_admissibleFrame_of_near hQ hu (hproj b hbS) (hproj a ha) (hHS a ha b hbS)
      (by rwa [norm_sub_rev])

end Admissible


/-! ## Smooth local lifts -/

section Lift

variable {Q : H →L[ℂ] H}

/-- The correction `E(D) = Q D u₀` of the local lift. -/
def liftCorr (Q u₀ : H →L[ℂ] H) (D : HSpace ℂ H) : H →L[ℂ] H := Q * D.op * u₀

/-- The Hilbert–Schmidt displacement `w(D) − Q` of the local lift
`w(D) = (P₀ + D) u₀ (1 + E(D))⁻¹`, written as `(1 − Q) D u₀ (1 + E)⁻¹ + Y₀ (1 + E)⁻¹`. -/
def liftY (Q u₀ : H →L[ℂ] H) (Y₀ D : HSpace ℂ H) : HSpace ℂ H :=
  HSpace.rmulL (HSpace.lmulL (1 - Q) D) (u₀ * Ring.inverse (1 + liftCorr Q u₀ D)) +
    HSpace.rmulL Y₀ (Ring.inverse (1 + liftCorr Q u₀ D))

theorem norm_liftCorr_lt (hQ : IsStarProjection Q) {u₀ : H →L[ℂ] H} {D : HSpace ℂ H}
    (hD : ‖D.op‖ * (‖u₀‖ + 1) < 1) : ‖liftCorr Q u₀ D‖ < 1 := by
  have hQn := IsStarProjection.norm_le Q hQ
  calc ‖liftCorr Q u₀ D‖ ≤ ‖Q‖ * ‖D.op‖ * ‖u₀‖ := by
        unfold liftCorr
        refine (norm_mul_le _ _).trans ?_
        gcongr
        exact norm_mul_le _ _
    _ ≤ 1 * ‖D.op‖ * (‖u₀‖ + 1) := by gcongr; linarith
    _ < 1 := by simpa using hD

/-- **The local lift is an admissible frame.**  For a frame `u₀ = Q + Y₀` of `P₀` and a
Hilbert–Schmidt displacement `D` with `P₀ + D` an orthogonal projection and
`‖D‖ (‖u₀‖ + 1) < 1`, the operator `Q + liftY D` is a frame of `P₀ + D` whose `ran Q`-defect is
`(Q u₀ − Q)(1 + E)⁻¹`. -/
theorem liftY_isFrameOf (hQ : IsStarProjection Q) {u₀ P₀ : H →L[ℂ] H} {Y₀ D : HSpace ℂ H}
    (hu₀ : IsFrameOf Q u₀ P₀) (hY₀ : Y₀.op = u₀ - Q) (hP₀ : IsStarProjection P₀)
    (hP : IsStarProjection (P₀ + D.op)) (hD : ‖D.op‖ * (‖u₀‖ + 1) < 1) :
    IsFrameOf Q (Q + (liftY Q u₀ Y₀ D).op) (P₀ + D.op) ∧
      Q * (Q + (liftY Q u₀ Y₀ D).op) - Q =
        (Q * u₀ - Q) * Ring.inverse (1 + liftCorr Q u₀ D) := by
  have hQi := hQ.isIdempotentElem
  set E := liftCorr Q u₀ D
  have hu₀Q : u₀ * Q = u₀ := hu₀.1
  have hPu : P₀ * u₀ = u₀ := by
    rw [← hu₀.2.2]; exact frameProj_mul_frame hQi hu₀Q (Ring.inverse_mul_cancel _ hu₀.2.1)
  have hQE : Q * E = E := by simp only [E, liftCorr, ← mul_assoc, hQi.eq]
  have hEQ : E * Q = E := by simp only [E, liftCorr, mul_assoc, hu₀Q]
  have hE : IsUnit (1 + E) := isUnit_one_add_of_norm_lt (norm_liftCorr_lt hQ hD)
  have hnear : ‖(P₀ + D.op) - P₀‖ < 1 := by
    rw [add_sub_cancel_left]
    have : ‖D.op‖ ≤ ‖D.op‖ * (‖u₀‖ + 1) := le_mul_of_one_le_right (norm_nonneg _)
      (by linarith [norm_nonneg u₀])
    linarith
  obtain ⟨hT, hT₀⟩ := isUnit_compression_of_norm_lt hP hP₀ hnear
  obtain ⟨hfr, hdef⟩ := isFrameOf_transfer hQ.isSelfAdjoint hQi hu₀ hP.isSelfAdjoint
    hP.isIdempotentElem hQE hEQ hE hT hT₀
  set B := Ring.inverse (1 + E)
  have hB' : (1 + E) * B = 1 := Ring.mul_inverse_cancel _ hE
  have hw : Q + (liftY Q u₀ Y₀ D).op = (P₀ + D.op) * u₀ * B := by
    simp only [liftY, HSpace.op_add, HSpace.op_rmulL, HSpace.op_lmulL, hY₀]
    have h1 : Q * (1 + E) * B = Q := by rw [mul_assoc, hB', mul_one]
    calc Q + ((1 - Q) * D.op * (u₀ * B) + (u₀ - Q) * B)
        = (P₀ * u₀) * B + D.op * u₀ * B + (Q - (Q + Q * D.op * u₀) * B) := by
          rw [hPu]; noncomm_ring
      _ = (P₀ + D.op) * u₀ * B := by
          rw [show Q + Q * D.op * u₀ = Q * (1 + E) by rw [mul_add, mul_one, hQE]; rfl, h1]
          noncomm_ring
  rw [hw]
  refine ⟨hfr, ?_⟩
  rw [hdef]
  congr 1
  simp only [E, liftCorr, mul_add, add_mul]
  rw [mul_assoc Q P₀ u₀, hPu]; noncomm_ring

/-- The local lift depends smoothly on the Hilbert–Schmidt displacement. -/
theorem contDiffAt_liftY {u₀ : H →L[ℂ] H} {Y₀ D₀ : HSpace ℂ H} {n : WithTop ℕ∞}
    (hunit : IsUnit (1 + liftCorr Q u₀ D₀)) : ContDiffAt ℝ n (liftY Q u₀ Y₀) D₀ := by
  have hop : ContDiff ℝ n (fun D : HSpace ℂ H => D.op) :=
    ((HSpace.opCLM H).restrictScalars ℝ).contDiff
  have hcorr : ContDiff ℝ n (fun D : HSpace ℂ H => liftCorr Q u₀ D) := by
    have := ((mulLeftRight ℝ (H →L[ℂ] H)) Q u₀).contDiff.comp hop
    exact this
  obtain ⟨x, hx⟩ := hunit
  have hB : ContDiffAt ℝ n (fun D => Ring.inverse (1 + liftCorr Q u₀ D)) D₀ := by
    have h1 : ContDiffAt ℝ n (fun D => 1 + liftCorr Q u₀ D) D₀ :=
      (contDiff_const.add hcorr).contDiffAt
    have h2 : ContDiffAt ℝ n Ring.inverse (1 + liftCorr Q u₀ D₀) := by
      rw [← hx]; exact contDiffAt_ringInverse ℝ x
    exact h2.comp D₀ h1
  have hA : ContDiffAt ℝ n (fun D => HSpace.rmulL (HSpace.lmulL (1 - Q) D)) D₀ :=
    (HSpace.rmulL.contDiff.comp (HSpace.lmulL (1 - Q)).contDiff).contDiffAt
  have hY : ContDiffAt ℝ n (fun _ : HSpace ℂ H => HSpace.rmulL Y₀) D₀ := contDiffAt_const
  exact (hA.clm_apply (contDiffAt_const.mul hB)).add (hY.clm_apply hB)

end Lift

end

end GaloisForLFunctions.HTGeometry
