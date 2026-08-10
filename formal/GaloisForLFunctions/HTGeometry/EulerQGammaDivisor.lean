import GaloisForLFunctions.HTGeometry.EulerQGammaContinuation

/-!
# The exact Cartier-divisor landing of the Euler q-Gamma response

The unconditional translation law `ζ(σ)·F^{K+1}_σ(s) = ζ(σ(1+s))·F^K_σ(s+1)` is an identity of
meromorphic germs, so taking meromorphic orders at a point turns it into the divisor
transgression: the order of the response jumps across the unit translation by exactly the
pulled-back order of `ζ`.

The order calculus needs one piece of infrastructure mathlib does not have — the invariance of
`meromorphicOrderAt` under an affine substitution — which is proved here from the
`meromorphicOrderAt_eq_int_iff` normal form.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

set_option maxHeartbeats 1000000

noncomputable section

/-! ## Orders under an affine substitution -/

theorem tendsto_affine_nhdsWithin {a b : ℂ} (ha : a ≠ 0) (s : ℂ) :
    Tendsto (fun z : ℂ => a * z + b) (𝓝[≠] s) (𝓝[≠] (a * s + b)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · exact (Continuous.tendsto (by fun_prop) s).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
    intro hEq
    exact hz (mul_left_cancel₀ ha (by linear_combination hEq))

/-- **The meromorphic order is invariant under an affine substitution.** -/
theorem meromorphicOrderAt_comp_affine {f : ℂ → ℂ} {a b : ℂ} (ha : a ≠ 0) (s : ℂ)
    (hf : MeromorphicAt f (a * s + b)) :
    meromorphicOrderAt (fun z : ℂ => f (a * z + b)) s = meromorphicOrderAt f (a * s + b) := by
  have hcomp : MeromorphicAt (fun z : ℂ => f (a * z + b)) s := meromorphicAt_comp_affine ha hf
  have haff : AnalyticAt ℂ (fun z : ℂ => a * z + b) s :=
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  rcases eq_or_ne (meromorphicOrderAt f (a * s + b)) ⊤ with htop | hne
  · rw [htop, meromorphicOrderAt_eq_top_iff]
    rw [meromorphicOrderAt_eq_top_iff] at htop
    exact (tendsto_affine_nhdsWithin ha s).eventually htop
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hn, meromorphicOrderAt_eq_int_iff hcomp]
    obtain ⟨g, hg, hg0, hgeq⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hn.symm
    refine ⟨fun z : ℂ => a ^ n * g (a * z + b), ?_, ?_, ?_⟩
    · have hcomp2 : AnalyticAt ℂ (fun z : ℂ => g (a * z + b)) s :=
        AnalyticAt.comp (g := g) (f := fun z : ℂ => a * z + b) hg haff
      exact analyticAt_const.mul hcomp2
    · exact mul_ne_zero (zpow_ne_zero n ha) hg0
    · have hpull := (tendsto_affine_nhdsWithin ha s).eventually hgeq
      filter_upwards [hpull] with z hz
      rw [hz]
      have hstep : a * z + b - (a * s + b) = a * (z - s) := by ring
      rw [hstep, mul_zpow]
      simp only [smul_eq_mul]
      ring

/-! ## The zeta factor of the translation law -/

theorem meromorphicAt_zeta_exponent (σ : EulerSigma) (s : ℂ) :
    MeromorphicAt (fun z : ℂ => riemannZeta (eqgExponent σ z)) s := by
  have hfun : (fun z : ℂ => riemannZeta (eqgExponent σ z))
      = fun z : ℂ => riemannZeta ((σ.val : ℂ) * z + (σ.val : ℂ)) := by
    funext z
    rw [eqgExponent]
    congr 1
    ring
  rw [hfun]
  exact meromorphicAt_comp_affine (sigma_ne_zero σ) (meromorphicAt_riemannZeta _)

theorem meromorphicOrderAt_zeta_exponent (σ : EulerSigma) (a : ℂ) :
    meromorphicOrderAt (fun z : ℂ => riemannZeta (eqgExponent σ z)) a
      = meromorphicOrderAt riemannZeta (eqgExponent σ a) := by
  have hfun : (fun z : ℂ => riemannZeta (eqgExponent σ z))
      = fun z : ℂ => riemannZeta ((σ.val : ℂ) * z + (σ.val : ℂ)) := by
    funext z
    rw [eqgExponent]
    congr 1
    ring
  have harg : (σ.val : ℂ) * a + (σ.val : ℂ) = eqgExponent σ a := by
    rw [eqgExponent]
    ring
  rw [hfun, meromorphicOrderAt_comp_affine (sigma_ne_zero σ) a
    (by rw [harg]; exact meromorphicAt_riemannZeta _), harg]

/-! ## The unit translate -/

theorem meromorphicAt_eqgCont_succ_arg (σ : EulerSigma) (K : ℕ) {a : ℂ}
    (hK : 1 < (eqgArg σ K (a + 1)).re) :
    MeromorphicAt (fun z : ℂ => eqgCont σ K (z + 1)) a := by
  have hfun : (fun z : ℂ => eqgCont σ K (z + 1))
      = fun z : ℂ => eqgCont σ K (1 * z + 1) := by
    funext z
    rw [one_mul]
  rw [hfun]
  refine meromorphicAt_comp_affine one_ne_zero ?_
  rw [one_mul]
  exact meromorphicAt_eqgCont σ K hK

theorem meromorphicOrderAt_eqgCont_succ_arg (σ : EulerSigma) (K : ℕ) {a : ℂ}
    (hK : 1 < (eqgArg σ K (a + 1)).re) :
    meromorphicOrderAt (fun z : ℂ => eqgCont σ K (z + 1)) a
      = meromorphicOrderAt (eqgCont σ K) (a + 1) := by
  have hfun : (fun z : ℂ => eqgCont σ K (z + 1))
      = fun z : ℂ => eqgCont σ K (1 * z + 1) := by
    funext z
    rw [one_mul]
  rw [hfun, meromorphicOrderAt_comp_affine one_ne_zero a
    (by rw [one_mul]; exact meromorphicAt_eqgCont σ K hK), one_mul]

/-! ## The divisor transgression -/

theorem eqgArg_succ_shift (σ : EulerSigma) (K : ℕ) (a : ℂ) :
    eqgArg σ K (a + 1) = eqgArg σ (K + 1) a := by
  rw [eqgArg, eqgArg, eqgExponent, eqgExponent]
  push_cast
  ring

/-- **Theorem 6.1, equation (EQG.17).**  The order of the Euler q-Gamma response jumps across the
unit translation by exactly the pulled-back order of `ζ`. -/
theorem eqgCont_order_transgression (σ : EulerSigma) (K : ℕ) {a : ℂ}
    (hK : 1 < (eqgArg σ (K + 1) a).re) :
    meromorphicOrderAt (eqgCont σ (K + 1)) a
      = meromorphicOrderAt riemannZeta (eqgExponent σ a)
        + meromorphicOrderAt (eqgCont σ K) (a + 1) := by
  have hK' : 1 < (eqgArg σ K (a + 1)).re := by
    rw [eqgArg_succ_shift]
    exact hK
  have hleft : MeromorphicAt (eqgCont σ (K + 1)) a := meromorphicAt_eqgCont σ (K + 1) hK
  have hconstL : MeromorphicAt (fun _ : ℂ => riemannZeta (σ.val : ℂ)) a :=
    analyticAt_const.meromorphicAt
  have hzeta : MeromorphicAt (fun z : ℂ => riemannZeta (eqgExponent σ z)) a :=
    meromorphicAt_zeta_exponent σ a
  have hshift : MeromorphicAt (fun z : ℂ => eqgCont σ K (z + 1)) a :=
    meromorphicAt_eqgCont_succ_arg σ K hK'
  have hfun : ((fun _ : ℂ => riemannZeta (σ.val : ℂ)) * eqgCont σ (K + 1))
      = ((fun z : ℂ => riemannZeta (eqgExponent σ z)) * fun z : ℂ => eqgCont σ K (z + 1)) := by
    funext z
    exact eqgCont_translation σ K z
  have hord := congrArg (fun h : ℂ → ℂ => meromorphicOrderAt h a) hfun
  rw [meromorphicOrderAt_mul hconstL hleft, meromorphicOrderAt_mul hzeta hshift] at hord
  rw [meromorphicOrderAt_const] at hord
  rw [if_neg (zeta_sigma_ne_zero σ), zero_add] at hord
  rw [hord, meromorphicOrderAt_zeta_exponent, meromorphicOrderAt_eqgCont_succ_arg σ K hK']

end

end GaloisForLFunctions.HTGeometry
