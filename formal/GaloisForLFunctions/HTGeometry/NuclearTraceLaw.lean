/-
# Nuclear trace law

The approximation-number trace norm is exactly the ordinary operator trace of the absolute
value.  The proof keeps the complete singular-value sequence, including multiplicity: extend the
live right singular vectors to a Hilbert basis, use Schatten-one factorization for basis
independence of the trace, kill the orthogonal complement by SVD completeness, and reindex the
remaining diagonal by the live singular indices.
-/
import GaloisForLFunctions.RHTower.TraceClassCyclicity

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The trace of the absolute value is the sum of all singular values, with multiplicity. -/
theorem opTrace_absOp_eq_tsum_singVal {T : H →L[ℂ] H}
    (hT : MemSchattenClass 1 T) :
    opTrace (absOp T) = ∑' n, ((singVal T n : ℝ) : ℂ) := by
  classical
  have hcpt : IsCompactOperator T := hT.isCompactOperator one_pos
  have hsing_of_sv : ∀ n, svVal (energyOp T) n ≠ 0 → singVal T n ≠ 0 := by
    intro n hμ hs
    apply hμ
    rw [← singVal_sq T n, hs]
    ring
  have hsv_of_sing : ∀ n, singVal T n ≠ 0 → svVal (energyOp T) n ≠ 0 := by
    intro n hs hμ
    exact hs (by rw [singVal, hμ, Real.sqrt_zero])
  have hlive_unit : ∀ n, singVal T n ≠ 0 → ‖svVec (energyOp T) n‖ = 1 := by
    intro n hn
    exact norm_svVec_of_ne_zero (energyOp_compact hcpt) (energyOp_symmetric T)
      (energyOp_pos T) (hsv_of_sing n hn)
  obtain ⟨w, b, hAw, hb⟩ := exists_svVec_extension hcpt
  have horthw : ∀ u ∈ w, ∀ v ∈ w, u ≠ v → inner ℂ u v = 0 := by
    have hw_orth : Orthonormal ℂ (Subtype.val : w → H) := hb ▸ b.orthonormal
    rw [orthonormal_subtype_iff_ite] at hw_orth
    intro u hu v hv huv
    have h := hw_orth u hu v hv
    rwa [if_neg huv] at h
  let R := traceClassRoot T
  have hR : R.IsHilbertSchmidt := traceClassRoot_isHilbertSchmidt hT
  have hfac : R ∘L R = absOp T := traceClassRoot_comp_self T
  have htrace : opTrace (absOp T) =
      ∑' v : w, inner ℂ (v : H) (absOp T (v : H)) := by
    rw [← hfac, opTrace_comp_eq_tsum_basis hR hR b]
    exact tsum_congr fun v => by rw [show b v = (v : H) from congrFun hb v, hfac]
  rw [htrace]
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun p => ⟨svVec (energyOp T) p.1,
      hAw ⟨p.1, hsv_of_sing p.1 ?_, rfl⟩⟩) ?_ ?_ ?_
  · have hp := p.2
    simpa only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero] using hp
  · rintro ⟨m, hm⟩ ⟨n, hn⟩ hmn
    simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero] at hm hn
    exact Subtype.ext
      (svVec_live_injective hcpt (hsv_of_sing n hn) (congrArg Subtype.val hmn))
  · rintro ⟨u, hu⟩ hfu
    simp only [Function.mem_support, ne_eq] at hfu
    have huA : u ∈ svVec (energyOp T) '' {n | svVal (energyOp T) n ≠ 0} := by
      by_contra huA
      have horth_all : ∀ n, inner ℂ (svVec (energyOp T) n) u = 0 := by
        intro n
        rcases eq_or_ne (svVal (energyOp T) n) 0 with h0 | hne
        · rw [svVec_eq_zero_of_svVal_eq_zero (energyOp T) h0]
          exact inner_zero_left _
        · have hmem : svVec (energyOp T) n ∈ w := hAw ⟨n, hne, rfl⟩
          refine horthw _ hmem _ hu fun h => huA ?_
          rw [← h]
          exact ⟨n, hne, rfl⟩
      have hTu : T u = 0 := apply_eq_zero_of_forall_inner_svVec_energyOp hcpt horth_all
      have habsu : absOp T u = 0 := by
        apply norm_eq_zero.mp
        rw [norm_absOp_apply, hTu, norm_zero]
      exact hfu (by rw [habsu, inner_zero_right])
    obtain ⟨n, hn, hun⟩ := huA
    refine ⟨⟨n, ?_⟩, Subtype.ext hun⟩
    simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
    exact hsing_of_sv n hn
  · rintro ⟨n, hn⟩
    simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero] at hn
    show inner ℂ (svVec (energyOp T) n)
        (absOp T (svVec (energyOp T) n)) = ((singVal T n : ℝ) : ℂ)
    rw [absOp_apply_svVec, inner_smul_right, inner_self_eq_norm_sq_to_K,
      hlive_unit n hn]
    norm_num

/-- The approximation-number trace norm, cast to `ℂ`, is the trace of the absolute value. -/
theorem ofReal_traceNorm_eq_opTrace_absOp {T : H →L[ℂ] H}
    (hT : MemSchattenClass 1 T) :
    ((traceNorm H T : ℝ) : ℂ) = opTrace (absOp T) := by
  have hcpt : IsCompactOperator T := hT.isCompactOperator one_pos
  rw [opTrace_absOp_eq_tsum_singVal hT]
  unfold traceNorm
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun n => congrArg Complex.ofReal (approxNumber_eq_singVal hcpt n)

/-- **Nuclear trace law:** `‖T‖₁ = Re Tr |T|` for every Schatten-one operator. -/
theorem traceNorm_eq_re_opTrace_absOp {T : H →L[ℂ] H}
    (hT : MemSchattenClass 1 T) :
    traceNorm H T = (opTrace (absOp T)).re := by
  have h := congrArg Complex.re (ofReal_traceNorm_eq_opTrace_absOp hT)
  simpa using h

end RHTower
