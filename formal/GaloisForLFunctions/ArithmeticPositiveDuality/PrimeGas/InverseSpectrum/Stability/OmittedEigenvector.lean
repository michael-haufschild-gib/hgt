import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.TraceBound
import GaloisForLFunctions.HTGeometry.CompactSelfAdjointEigenvalue
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact
import GaloisForLFunctions.HTGeometry.ProjectionSumCalkinLift

/-! # An omitted wave detecting the squared propagation error

The top eigenvector of the compressed square heat splits its second
moment between the missing and retained subspaces. Both components
are measured by the fourth-trace deficit.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem top_positive_wave {T : H →L[ℂ] H} (hc : T.IsHilbertSchmidt)
    (hp : T.IsPositive) (hn : T ≠ 0) : ∃ f : H, ‖f‖ = 1 ∧ T f = (‖T‖:ℂ) • f := by
  obtain ⟨μ,f,he,hu,hf⟩ := exists_unit_eigenvector_norm hc.isCompactOperator hp.isSymmetric hn
  have h := hp.re_inner_nonneg_right f
  change 0 ≤ (inner ℂ f (T f)).re at h
  rw [hf,inner_smul_right,inner_self_eq_norm_sq_to_K,hu] at h
  simp only [RCLike.ofReal_one,one_pow,mul_one,Complex.ofReal_re] at h
  rw [abs_of_nonneg h] at he
  exact ⟨f,hu,he ▸ hf⟩

private theorem adjoint_unit_reading {T : H →L[ℂ] H} (hs : T.IsHilbertSchmidt)
    {f : H} (hf : ‖f‖ = 1) : ‖(star T) f‖^2 ≤ hsNormSq T := by
  have h := (star T).le_opNorm f
  rw [hf,mul_one,norm_star] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) (h.trans (norm_le_hsNorm hs)) 2).trans_eq (sq_hsNorm T)

private theorem compression_norm (G : Propagator) (U : Gas →ₗᵢ[ℂ] Gas)
    (hu : G.val = criticalOperator*U.toContinuousLinearMap) :
    ‖criticalOperator^2-G.val^2‖ = ‖omitted U*squareHeat.val*omitted U‖ := by
  let D := criticalOperator
  let V := U.toContinuousLinearMap
  let Q := omitted U
  have hD : star D = D := critical_isPositive.isSelfAdjoint.star_eq
  have hQ : star Q = Q := omitted_self U
  have hQQ : Q*Q = Q := omitted_idempotent U
  have hfirst : D^2-G.val^2 = star (Q*D)*(Q*D) := by
    rw [show G.val^2 = G.val*star G.val by rw [G.property.1.isSelfAdjoint.star_eq,pow_two],hu]
    change D^2-(D*V)*star (D*V) = star (Q*D)*(Q*D)
    rw [star_mul,star_mul,hD,hQ,mul_assoc D Q (Q*D),← mul_assoc Q Q D,hQQ]
    change D^2-(D*V)*(star V*D) = D*((1-V*star V)*D)
    noncomm_ring
  have hsecond : (Q*D)*star (Q*D) = Q*squareHeat.val*Q := by
    change (Q*D)*star (Q*D) = Q*D^2*Q
    rw [star_mul,hD,hQ,pow_two]
    noncomm_ring
  calc
    ‖D^2-G.val^2‖ = ‖star (Q*D)*(Q*D)‖ := congrArg norm hfirst
    _ = ‖(Q*D)*star (Q*D)‖ := (CStarRing.norm_star_mul_self (x := Q*D)).trans
      (CStarRing.norm_self_mul_star (x := Q*D)).symm
    _ = _ := congrArg norm hsecond

private theorem top_compression {D : H →L[ℂ] H} (hD : D.IsPositive) (hs : (D^2).IsHilbertSchmidt)
    (Q : H →L[ℂ] H) (hQ : IsStarProjection Q) (hn : Q*D^2*Q ≠ 0) :
    ∃ f : H, ‖f‖ = 1 ∧ Q f = f ∧ Q ((D^2 : H →L[ℂ] H) f) = (‖Q*D^2*Q‖:ℂ) • f ∧ ‖D f‖^2 = ‖Q*D^2*Q‖ := by
  let A := D^2
  let K := Q*A*Q
  have hpos : K.IsPositive := by
    have he : K = star (D*Q)*(D*Q) := by
      change Q*D^2*Q = star (D*Q)*(D*Q)
      rw [star_mul,hQ.isSelfAdjoint.star_eq,hD.isSelfAdjoint.star_eq,pow_two]
      noncomm_ring
    rw [he]
    exact isPositive_adjoint_comp_self _
  have htop : 0 < ‖K‖ := norm_pos_iff.mpr hn
  obtain ⟨f,hf,he⟩ := top_positive_wave (T := K) ((hs.comp_left Q).comp_right Q)
    hpos (norm_pos_iff.mp htop)
  have qfix : Q f = f := by
    have hi : Q*K = K := by
      change Q*(Q*A*Q) = Q*A*Q
      calc
        _ = (Q*Q)*A*Q := by noncomm_ring
        _ = _ := by rw [hQ.isIdempotentElem.eq]
    have h := congrArg (fun T : H →L[ℂ] H => T f) hi
    change Q (K f) = K f at h
    rw [he,map_smul] at h
    have hinv := congrArg (fun u : H => (‖K‖:ℂ)⁻¹ • u) h
    simpa only [smul_smul,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr htop.ne'),one_smul] using hinv
  have hproj : Q (A f) = (‖K‖:ℂ) • f := by
    change Q (A (Q f)) = _ at he
    rwa [qfix] at he
  have hmoment : ‖D f‖^2 = ‖K‖ := by
    have h := congrArg Complex.re (adjoint_inner_left D f (D f))
    rw [show adjoint D = D from hD.isSelfAdjoint.star_eq] at h
    change (inner ℂ (A f) f).re = (inner ℂ (D f) (D f)).re at h
    have hh : inner ℂ (Q (A f)) f = inner ℂ (A f) (Q f) := hQ.isSelfAdjoint.isSymmetric (A f) f
    rw [qfix,hproj,inner_smul_left,inner_self_eq_norm_sq_to_K,hf] at hh
    have hsqr : (inner ℂ (D f) (D f)).re = ‖D f‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
    rw [hsqr,← hh] at h
    simpa only [RCLike.ofReal_one,one_pow,mul_one,Complex.conj_ofReal,Complex.ofReal_re] using h.symm
  exact ⟨f,hf,qfix,hproj,hmoment⟩

private theorem top_moment_bound (U : H →ₗᵢ[ℂ] H) (A : HSObservable H)
    (f : H) (hf : ‖f‖ = 1) (qfix : omitted U f = f) (weight : ℝ) (htop : 0 ≤ weight)
    (hproj : omitted U (A.val f) = (weight:ℂ) • f) :
    2*‖A.val f‖^2 ≤ hsNormSq (omitted U*A.val)+
      hsNormSq (omitted U*(A.val*U.toContinuousLinearMap))+weight^2 := by
  let Q := omitted U
  let V := U.toContinuousLinearMap
  have hQ : IsStarProjection Q := ⟨omitted_idempotent U,omitted_self U⟩
  have hA := A.property.1.star_eq
  have hfirst := adjoint_unit_reading (A.property.2.comp_left Q) hf
  have hsecond := adjoint_unit_reading ((A.property.2.comp_right V).comp_left Q) hf
  change ‖(star (Q*A.val)) f‖^2 ≤ _ at hfirst
  change ‖(star (Q*(A.val*V))) f‖^2 ≤ _ at hsecond
  rw [star_mul,hA,hQ.isSelfAdjoint.star_eq] at hfirst
  rw [star_mul,star_mul,hA,hQ.isSelfAdjoint.star_eq] at hsecond
  change ‖A.val (Q f)‖^2 ≤ _ at hfirst
  change ‖(star V) (A.val (Q f))‖^2 ≤ _ at hsecond
  rw [qfix] at hfirst hsecond
  have hp := HTGeometry.TightFormation.norm_sq_eq_of_isStarProjection hQ (A.val f)
  have hr : A.val f-Q (A.val f) = U ((star V) (A.val f)) := by
    change A.val f-(A.val f-V ((star V) (A.val f))) = _
    exact sub_sub_cancel _ _
  rw [hr,U.norm_map,hproj,norm_smul,Complex.norm_real,Real.norm_of_nonneg htop,hf,mul_one] at hp
  change ‖A.val f‖^2 ≤ hsNormSq (Q*A.val) at hfirst
  change ‖(star V) (A.val f)‖^2 ≤ hsNormSq (Q*(A.val*V)) at hsecond
  change 2*‖A.val f‖^2 ≤ hsNormSq (Q*A.val)+hsNormSq (Q*(A.val*V))+weight^2
  linarith only [hfirst,hsecond,hp]

/-- A nonzero squared propagation error supplies one unit wave and two measured energy moments. -/
theorem omitted_top_moments (G : Propagator) (hn : criticalOperator^2-G.val^2 ≠ 0) :
    ∃ f : Gas, ‖f‖ = 1 ∧ ‖criticalOperator f‖^2 = ‖criticalOperator^2-G.val^2‖ ∧
      2*‖squareHeat.val f‖^2 ≤ traceLoss G.val+‖criticalOperator^2-G.val^2‖^2 := by
  obtain ⟨U,hu,_⟩ := (full_isometry_iff G.val).mp G.property.2
  let Q := omitted U
  let K := Q*squareHeat.val*Q
  have hQ : IsStarProjection Q := ⟨omitted_idempotent U,omitted_self U⟩
  have hK : ‖criticalOperator^2-G.val^2‖ = ‖K‖ := compression_norm G U hu
  have htop : 0 < ‖K‖ := hK ▸ norm_pos_iff.mpr hn
  obtain ⟨f,hf,hfix,hproj,hm⟩ := top_compression critical_isPositive squareHeat.property.2 Q hQ (norm_pos_iff.mp htop)
  have hb := top_moment_bound U squareHeat f hf hfix ‖K‖ htop.le hproj
  have ht := fourth_trace_defect U
  rw [← hu,fourthMoment_of_positive G.property.1] at ht
  change traceLoss G.val = _ at ht
  rw [← ht] at hb
  exact ⟨f,hf,hm.trans hK.symm,hK.symm ▸ hb⟩

#print axioms omitted_top_moments

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
