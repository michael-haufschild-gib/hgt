import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# Critical-locus quadruple evenness and the universal criticality law

An off-line splitting quadruple `{1/2 ± t ± γi}` is invariant, as a multiset, under the
displacement sign flip `t ↦ -t`.  Consequently every function of the configuration — any
value type, no regularity — is even in the displacement, and every scalar quadruple
functional has vanishing derivative at the critical locus: the first-order theory of every
spectral criterion degenerates identically.  The second central jet is the first surviving
information; for the completed source `XiC` it is exactly twice the sum of the two second
derivatives at the conjugate pair.

All statements are hypothesis-free: evenness and criticality hold for arbitrary `F` (the
derivative statement uses the junk-value calculus), and the jet identities are instantiated
at the corpus's entire `XiC`.
-/

namespace RHTower

noncomputable section

open Complex

/-- The off-line splitting quadruple at ordinate `γ` with displacement `t`. -/
def criticalQuadruple (γ t : ℂ) : Multiset ℂ :=
  {t + (1 / 2 + γ * I), (1 / 2 + γ * I) - t, t + (1 / 2 - γ * I), (1 / 2 - γ * I) - t}

/-- **Quadruple evenness.**  The splitting quadruple is invariant under `t ↦ -t` as a
multiset. -/
theorem criticalQuadruple_neg (γ t : ℂ) :
    criticalQuadruple γ (-t) = criticalQuadruple γ t := by
  unfold criticalQuadruple
  have h1 : -t + (1 / 2 + γ * I) = (1 / 2 + γ * I) - t := by ring
  have h2 : (1 / 2 + γ * I) - -t = t + (1 / 2 + γ * I) := by ring
  have h3 : -t + (1 / 2 - γ * I) = (1 / 2 - γ * I) - t := by ring
  have h4 : (1 / 2 - γ * I) - -t = t + (1 / 2 - γ * I) := by ring
  rw [h1, h2, h3, h4]
  change (((1 / 2 + γ * I) - t) ::ₘ (t + (1 / 2 + γ * I)) ::ₘ
      ((1 / 2 - γ * I) - t) ::ₘ (t + (1 / 2 - γ * I)) ::ₘ 0) =
    ((t + (1 / 2 + γ * I)) ::ₘ ((1 / 2 + γ * I) - t) ::ₘ
      (t + (1 / 2 - γ * I)) ::ₘ ((1 / 2 - γ * I) - t) ::ₘ 0)
  rw [Multiset.cons_swap]
  congr 2
  rw [Multiset.cons_swap]

/-- **Universal criticality, configuration form.**  Every function of the configuration —
arbitrary value type, no regularity — is even in the off-line displacement. -/
theorem apply_criticalQuadruple_neg {α : Sort*} (G : Multiset ℂ → α) (γ t : ℂ) :
    G (criticalQuadruple γ (-t)) = G (criticalQuadruple γ t) :=
  congrArg G (criticalQuadruple_neg γ t)

/-- The scalar quadruple functional of a test `F`. -/
def criticalQuadrupleSum (F : ℂ → ℂ) (γ t : ℂ) : ℂ :=
  F (t + (1 / 2 + γ * I)) + F ((1 / 2 + γ * I) - t) +
    F (t + (1 / 2 - γ * I)) + F ((1 / 2 - γ * I) - t)

/-- Evenness of the scalar quadruple functional, for arbitrary `F`. -/
theorem criticalQuadrupleSum_neg (F : ℂ → ℂ) (γ t : ℂ) :
    criticalQuadrupleSum F γ (-t) = criticalQuadrupleSum F γ t := by
  unfold criticalQuadrupleSum
  have h1 : -t + (1 / 2 + γ * I) = (1 / 2 + γ * I) - t := by ring
  have h2 : (1 / 2 + γ * I) - -t = t + (1 / 2 + γ * I) := by ring
  have h3 : -t + (1 / 2 - γ * I) = (1 / 2 - γ * I) - t := by ring
  have h4 : (1 / 2 - γ * I) - -t = t + (1 / 2 - γ * I) := by ring
  rw [h1, h2, h3, h4]
  ring

/-- **Universal criticality law.**  The derivative of every scalar quadruple functional
vanishes at the critical locus — for every `F`, with no differentiability assumption
(the junk-value calculus makes the statement unconditional). -/
theorem deriv_criticalQuadrupleSum_zero (F : ℂ → ℂ) (γ : ℂ) :
    deriv (criticalQuadrupleSum F γ) 0 = 0 := by
  have heven : (fun t : ℂ => criticalQuadrupleSum F γ (-t)) = criticalQuadrupleSum F γ := by
    funext t
    exact criticalQuadrupleSum_neg F γ t
  have hneg := deriv_comp_neg (criticalQuadrupleSum F γ) (0 : ℂ)
  rw [heven, neg_zero] at hneg
  have h2 : (2 : ℂ) * deriv (criticalQuadrupleSum F γ) 0 = 0 := by
    linear_combination hneg
  rcases mul_eq_zero.mp h2 with h | h
  · norm_num at h
  · exact h

/-- The `XiC` quadruple functional has an exact derivative at every displacement. -/
theorem hasDerivAt_criticalQuadrupleSum_XiC (γ t : ℂ) :
    HasDerivAt (criticalQuadrupleSum XiC γ)
      (deriv XiC (t + (1 / 2 + γ * I)) + -deriv XiC ((1 / 2 + γ * I) - t) +
        deriv XiC (t + (1 / 2 - γ * I)) + -deriv XiC ((1 / 2 - γ * I) - t)) t := by
  have hXi : Differentiable ℂ XiC := XiC_differentiable
  have h1 : HasDerivAt (fun s : ℂ => XiC (s + (1 / 2 + γ * I)))
      (deriv XiC (t + (1 / 2 + γ * I))) t := by
    simpa [Function.comp_def] using
      ((hXi (t + (1 / 2 + γ * I))).hasDerivAt.comp t
        ((hasDerivAt_id t).add_const (1 / 2 + γ * I)))
  have h2 : HasDerivAt (fun s : ℂ => XiC ((1 / 2 + γ * I) - s))
      (-deriv XiC ((1 / 2 + γ * I) - t)) t := by
    simpa [Function.comp_def] using
      ((hXi ((1 / 2 + γ * I) - t)).hasDerivAt.comp t
        ((hasDerivAt_id t).const_sub (1 / 2 + γ * I)))
  have h3 : HasDerivAt (fun s : ℂ => XiC (s + (1 / 2 - γ * I)))
      (deriv XiC (t + (1 / 2 - γ * I))) t := by
    simpa [Function.comp_def] using
      ((hXi (t + (1 / 2 - γ * I))).hasDerivAt.comp t
        ((hasDerivAt_id t).add_const (1 / 2 - γ * I)))
  have h4 : HasDerivAt (fun s : ℂ => XiC ((1 / 2 - γ * I) - s))
      (-deriv XiC ((1 / 2 - γ * I) - t)) t := by
    simpa [Function.comp_def] using
      ((hXi ((1 / 2 - γ * I) - t)).hasDerivAt.comp t
        ((hasDerivAt_id t).const_sub (1 / 2 - γ * I)))
  exact ((h1.add h2).add h3).add h4

/-- Exact first-derivative formula for the `XiC` quadruple functional. -/
theorem deriv_criticalQuadrupleSum_XiC (γ t : ℂ) :
    deriv (criticalQuadrupleSum XiC γ) t =
      deriv XiC (t + (1 / 2 + γ * I)) - deriv XiC ((1 / 2 + γ * I) - t) +
        (deriv XiC (t + (1 / 2 - γ * I)) - deriv XiC ((1 / 2 - γ * I) - t)) := by
  rw [(hasDerivAt_criticalQuadrupleSum_XiC γ t).deriv]
  ring

/-- **Second central jet of the `XiC` quadruple functional** — the first surviving
information at the critical locus: twice the sum of the two second derivatives at the
conjugate pair. -/
theorem iteratedDeriv_two_criticalQuadrupleSum_XiC (γ : ℂ) :
    iteratedDeriv 2 (criticalQuadrupleSum XiC γ) 0 =
      2 * (iteratedDeriv 2 XiC (1 / 2 + γ * I) + iteratedDeriv 2 XiC (1 / 2 - γ * I)) := by
  have hd : Differentiable ℂ (deriv XiC) := fun z =>
    (XiC_analytic.deriv z (Set.mem_univ z)).differentiableAt
  have hderiv_eq : deriv (criticalQuadrupleSum XiC γ) = fun t =>
      deriv XiC (t + (1 / 2 + γ * I)) - deriv XiC ((1 / 2 + γ * I) - t) +
        (deriv XiC (t + (1 / 2 - γ * I)) - deriv XiC ((1 / 2 - γ * I) - t)) :=
    funext fun t => deriv_criticalQuadrupleSum_XiC γ t
  have e1 : HasDerivAt (fun s : ℂ => deriv XiC (s + (1 / 2 + γ * I)))
      (deriv (deriv XiC) ((0 : ℂ) + (1 / 2 + γ * I))) 0 := by
    simpa [Function.comp_def] using
      ((hd ((0 : ℂ) + (1 / 2 + γ * I))).hasDerivAt.comp (0 : ℂ)
        ((hasDerivAt_id (0 : ℂ)).add_const (1 / 2 + γ * I)))
  have e2 : HasDerivAt (fun s : ℂ => deriv XiC ((1 / 2 + γ * I) - s))
      (-deriv (deriv XiC) ((1 / 2 + γ * I) - (0 : ℂ))) 0 := by
    simpa [Function.comp_def] using
      ((hd ((1 / 2 + γ * I) - (0 : ℂ))).hasDerivAt.comp (0 : ℂ)
        ((hasDerivAt_id (0 : ℂ)).const_sub (1 / 2 + γ * I)))
  have e3 : HasDerivAt (fun s : ℂ => deriv XiC (s + (1 / 2 - γ * I)))
      (deriv (deriv XiC) ((0 : ℂ) + (1 / 2 - γ * I))) 0 := by
    simpa [Function.comp_def] using
      ((hd ((0 : ℂ) + (1 / 2 - γ * I))).hasDerivAt.comp (0 : ℂ)
        ((hasDerivAt_id (0 : ℂ)).add_const (1 / 2 - γ * I)))
  have e4 : HasDerivAt (fun s : ℂ => deriv XiC ((1 / 2 - γ * I) - s))
      (-deriv (deriv XiC) ((1 / 2 - γ * I) - (0 : ℂ))) 0 := by
    simpa [Function.comp_def] using
      ((hd ((1 / 2 - γ * I) - (0 : ℂ))).hasDerivAt.comp (0 : ℂ)
        ((hasDerivAt_id (0 : ℂ)).const_sub (1 / 2 - γ * I)))
  have H : HasDerivAt (fun t : ℂ =>
      deriv XiC (t + (1 / 2 + γ * I)) - deriv XiC ((1 / 2 + γ * I) - t) +
        (deriv XiC (t + (1 / 2 - γ * I)) - deriv XiC ((1 / 2 - γ * I) - t)))
      (deriv (deriv XiC) ((0 : ℂ) + (1 / 2 + γ * I)) -
          -deriv (deriv XiC) ((1 / 2 + γ * I) - (0 : ℂ)) +
        (deriv (deriv XiC) ((0 : ℂ) + (1 / 2 - γ * I)) -
          -deriv (deriv XiC) ((1 / 2 - γ * I) - (0 : ℂ)))) 0 :=
    (e1.sub e2).add (e3.sub e4)
  have hiter : ∀ f : ℂ → ℂ, iteratedDeriv 2 f = deriv (deriv f) := by
    intro f
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  simp only [hiter]
  rw [hderiv_eq, H.deriv]
  simp only [zero_add, sub_zero]
  ring

end

end RHTower
