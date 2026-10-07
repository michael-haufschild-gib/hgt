import GaloisForLFunctions.HTGeometry.DiscreteDilationGerm

/-!
# A period from closed discrete fiber differences

For an entire homogeneous pair without common zeros, equality of fibers is expressed by a cross
determinant. If dilation preserves this relation, a regular nonzero return to the origin
forces a period whenever the differences in that fiber form a closed discrete set.

No rational multiplication map, integrality of the dilation, or reflection symmetry is assumed.
-/

namespace GaloisForLFunctions.HTGeometry.DiscreteFiberDilationPeriod

open Filter Topology Set DiscreteDilationGerm

def SameFiber (N D : ℂ → ℂ) (x y : ℂ) : Prop := N x * D y = N y * D x

def fiberDifferences (N D : ℂ → ℂ) : Set ℂ :=
  {u | ∃ x y, SameFiber N D x 0 ∧ SameFiber N D y 0 ∧ u = x - y}

theorem sameFiber_trans {N D : ℂ → ℂ} (hpair : ∀ z, N z ≠ 0 ∨ D z ≠ 0)
    {x y z : ℂ} (hxy : SameFiber N D x y) (hyz : SameFiber N D y z) :
    SameFiber N D x z := by
  dsimp [SameFiber] at *
  by_cases hy : D y = 0
  · have hNy := (hpair y).resolve_right (not_not.mpr hy)
    have hx : D x = 0 := by
      have : N y * D x = 0 := by simpa [hy] using hxy.symm
      exact (mul_eq_zero.mp this).resolve_left hNy
    have hz : D z = 0 := by
      have : N y * D z = 0 := by simpa [hy] using hyz
      exact (mul_eq_zero.mp this).resolve_left hNy
    simp [hx, hz]
  · apply mul_left_cancel₀ hy
    linear_combination D z * hxy + D x * hyz

theorem sameFiber_pow {N D : ℂ → ℂ} {lam : ℂ}
    (hscale : ∀ x y, SameFiber N D x y → SameFiber N D (lam * x) (lam * y))
    (n : ℕ) {x y : ℂ} (hxy : SameFiber N D x y) :
    SameFiber N D (lam ^ n * x) (lam ^ n * y) := by
  induction n with
  | zero => simpa using hxy
  | succ n ih => simpa [pow_succ', mul_assoc] using hscale _ _ ih

/-- The local deck branch is constructed separately below; this theorem consumes its actual
fiber identity and derives the period by discrete stabilization and analytic continuation. -/
theorem period_of_deck_germ {N D g : ℂ → ℂ} {lam tau b : ℂ}
    (hN : AnalyticOnNhd ℂ N univ) (hD : AnalyticOnNhd ℂ D univ)
    (hpair : ∀ z, N z ≠ 0 ∨ D z ≠ 0)
    (hlam : lam ≠ 0) (htau : tau ≠ 0) (hb : b ≠ 0)
    (hlim : Tendsto (fun n : ℕ => (lam ^ n)⁻¹) atTop (𝓝 0))
    (hscale : ∀ x y, SameFiber N D x y → SameFiber N D (lam * x) (lam * y))
    (hreturn : SameFiber N D tau 0)
    (hclosed : IsClosed (fiberDifferences N D)) (hdiscrete : IsDiscrete (fiberDifferences N D))
    (hg0 : g 0 = tau) (hgd : HasDerivAt g b 0)
    (hgerm : ∀ᶠ z in 𝓝 (0 : ℂ), SameFiber N D (g z) z) :
    ∀ z, SameFiber N D (z + (lam - 1) * tau) z := by
  have hsamples := shrinking_samples hlam htau hlim
  have hsmall := (tendsto_nhdsWithin_iff.mp hsamples).1.eventually hgerm
  have hmem : ∀ᶠ n in atTop,
      lam ^ n * (g (tau / lam ^ n) - g 0) ∈ fiberDifferences N D := by
    filter_upwards [hsmall] with n hn
    have hn0 := pow_ne_zero n hlam
    have hx := sameFiber_pow hscale n hn
    have hcancel : lam ^ n * (tau / lam ^ n) = tau := by field_simp
    rw [hcancel] at hx
    have hy := sameFiber_pow hscale n hreturn
    rw [mul_zero] at hy
    refine ⟨lam ^ n * g (tau / lam ^ n), lam ^ n * tau,
      sameFiber_trans hpair hx hreturn, hy, ?_⟩
    rw [hg0]
    ring
  have hs := eventually_affine_samples hgd hlam htau hlim hclosed hdiscrete hmem
  have hseq : ∀ᶠ n in atTop, SameFiber N D (tau + b * (tau / lam ^ n))
      (tau / lam ^ n) := by
    filter_upwards [hs, hsmall] with n hn hnf
    rwa [hn, hg0] at hnf
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), SameFiber N D (tau + b * z) z :=
    hsamples.frequently hseq.frequently
  have hleft : AnalyticOnNhd ℂ (fun z => N (tau + b * z) * D z) univ := by
    intro z _
    exact ((hN _ trivial).comp
      (analyticAt_const.add (analyticAt_const.mul analyticAt_id))).mul (hD z trivial)
  have hright : AnalyticOnNhd ℂ (fun z => N z * D (tau + b * z)) univ := by
    intro z _
    exact (hN z trivial).mul ((hD _ trivial).comp
      (analyticAt_const.add (analyticAt_const.mul analyticAt_id)))
  have hglobal : ∀ z, SameFiber N D (tau + b * z) z := by
    have heq := hleft.eq_of_frequently_eq hright hfreq
    exact fun z => congrFun heq z
  have hglobal' : ∀ z, SameFiber N D (lam * tau + b * z) z := by
    intro z
    have h := hscale _ _ (hglobal (z / lam))
    have h1 : lam * (z / lam) = z := by field_simp
    have h2 : lam * (tau + b * (z / lam)) = lam * tau + b * z := by field_simp
    rwa [h1, h2] at h
  intro z
  have h1 := hglobal ((z - tau) / b)
  have h2 := hglobal' ((z - tau) / b)
  have heq1 : tau + b * ((z - tau) / b) = z := by field_simp; ring
  have heq2 : lam * tau + b * ((z - tau) / b) = z + (lam - 1) * tau := by
    field_simp
    ring
  rw [heq1] at h1
  rw [heq2] at h2
  exact sameFiber_trans hpair h2 h1.symm

/-- A local inverse branch at a regular return, with its derivative formula and genuine fiber
identity. Only the finite chart containing the common value is used. -/
theorem exists_analytic_deck_germ {N D : ℂ → ℂ} {tau : ℂ}
    (hN : AnalyticOnNhd ℂ N univ) (hD : AnalyticOnNhd ℂ D univ)
    (hD0 : D 0 ≠ 0) (hDt : D tau ≠ 0) (hreturn : SameFiber N D tau 0)
    (hdert : deriv (fun z => N z / D z) tau ≠ 0) :
    ∃ g : ℂ → ℂ, ∃ b : ℂ, AnalyticAt ℂ g 0 ∧ g 0 = tau ∧ HasDerivAt g b 0 ∧
      b = (deriv (fun z => N z / D z) tau)⁻¹ * deriv (fun z => N z / D z) 0 ∧
      (∀ᶠ z in 𝓝 (0 : ℂ), SameFiber N D (g z) z) := by
  let H : ℂ → ℂ := fun z => N z / D z
  have hH0 : AnalyticAt ℂ H 0 := (hN 0 trivial).div (hD 0 trivial) hD0
  have hHt : AnalyticAt ℂ H tau := (hN tau trivial).div (hD tau trivial) hDt
  have hHval : H tau = H 0 := (div_eq_div_iff hDt hD0).mpr hreturn
  let i := hHt.hasStrictDerivAt.localInverse H (deriv H tau) tau hdert
  let g : ℂ → ℂ := fun z => i (H z)
  have hi0 : i (H 0) = tau := by
    rw [← hHval]
    exact (hHt.hasStrictDerivAt.eventually_left_inverse hdert).self_of_nhds
  have hid : HasDerivAt i (deriv H tau)⁻¹ (H 0) := by
    rw [← hHval]
    exact (hHt.hasStrictDerivAt.to_localInverse hdert).hasDerivAt
  have hgd : HasDerivAt g ((deriv H tau)⁻¹ * deriv H 0) 0 :=
    hid.comp 0 hH0.differentiableAt.hasDerivAt
  have hian : AnalyticAt ℂ i (H 0) := by
    rw [← hHval]
    exact hHt.analyticAt_localInverse hdert
  refine ⟨g, (deriv H tau)⁻¹ * deriv H 0, hian.comp hH0, hi0, hgd, rfl, ?_⟩
  have hright : ∀ᶠ w in 𝓝 (H 0), H (i w) = w := by
    rw [← hHval]
    exact hHt.hasStrictDerivAt.eventually_right_inverse hdert
  have heq := hH0.continuousAt.tendsto.eventually hright
  have hgn : Tendsto g (𝓝 0) (𝓝 tau) := by
    simpa only [show g 0 = tau from hi0] using hgd.continuousAt.tendsto
  have hDn := hgn.eventually ((hD tau trivial).continuousAt.eventually_ne hDt)
  filter_upwards [heq, hDn, (hD 0 trivial).continuousAt.eventually_ne hD0] with z hz hgz hDz
  exact (div_eq_div_iff hgz hDz).mp hz

theorem exists_deck_germ {N D : ℂ → ℂ} {tau : ℂ}
    (hN : AnalyticOnNhd ℂ N univ) (hD : AnalyticOnNhd ℂ D univ)
    (hD0 : D 0 ≠ 0) (hDt : D tau ≠ 0) (hreturn : SameFiber N D tau 0)
    (hder0 : deriv (fun z => N z / D z) 0 ≠ 0)
    (hdert : deriv (fun z => N z / D z) tau ≠ 0) :
    ∃ g : ℂ → ℂ, ∃ b : ℂ, b ≠ 0 ∧ g 0 = tau ∧ HasDerivAt g b 0 ∧
      (∀ᶠ z in 𝓝 (0 : ℂ), SameFiber N D (g z) z) := by
  obtain ⟨g, b, _, hg0, hgd, hb, hgerm⟩ := exists_analytic_deck_germ hN hD hD0 hDt hreturn hdert
  refine ⟨g, b, ?_, hg0, hgd, hgerm⟩
  rw [hb]
  exact mul_ne_zero (inv_ne_zero hdert) hder0

/-- Regularity at one nonzero return propagates to the origin: zero derivative would make the
local inverse branch constant after discrete stabilization, and hence make the entire pair constant. -/
theorem origin_deriv_ne {N D : ℂ → ℂ} {lam tau : ℂ}
    (hN : AnalyticOnNhd ℂ N univ) (hD : AnalyticOnNhd ℂ D univ)
    (hpair : ∀ z, N z ≠ 0 ∨ D z ≠ 0)
    (hD0 : D 0 ≠ 0) (hDt : D tau ≠ 0)
    (hdert : deriv (fun z => N z / D z) tau ≠ 0)
    (hlam : lam ≠ 0) (htau : tau ≠ 0)
    (hlim : Tendsto (fun n : ℕ => (lam ^ n)⁻¹) atTop (𝓝 0))
    (hscale : ∀ x y, SameFiber N D x y → SameFiber N D (lam * x) (lam * y))
    (hreturn : SameFiber N D tau 0)
    (hclosed : IsClosed (fiberDifferences N D)) (hdiscrete : IsDiscrete (fiberDifferences N D)) :
    deriv (fun z => N z / D z) 0 ≠ 0 := by
  intro hzero
  obtain ⟨g, b, hgan, hg0, hgd, hb, hgerm⟩ :=
    exists_analytic_deck_germ hN hD hD0 hDt hreturn hdert
  have hb0 : b = 0 := by rw [hb, hzero, mul_zero]
  have hsamples := shrinking_samples hlam htau hlim
  have hsmall := (tendsto_nhdsWithin_iff.mp hsamples).1.eventually hgerm
  have hmem : ∀ᶠ n in atTop,
      lam ^ n * (g (tau / lam ^ n) - g 0) ∈ fiberDifferences N D := by
    filter_upwards [hsmall] with n hn
    have hn0 := pow_ne_zero n hlam
    have hx := sameFiber_pow hscale n hn
    have hcancel : lam ^ n * (tau / lam ^ n) = tau := by field_simp
    rw [hcancel] at hx
    have hy := sameFiber_pow hscale n hreturn
    rw [mul_zero] at hy
    refine ⟨lam ^ n * g (tau / lam ^ n), lam ^ n * tau,
      sameFiber_trans hpair hx hreturn, hy, ?_⟩
    rw [hg0]
    ring
  have haffine := affine_germ_of_discrete_displacements hgan hgd hlam htau hlim
    hclosed hdiscrete hmem
  have hconst : ∀ᶠ z in 𝓝 (0 : ℂ), N tau * D z = N z * D tau := by
    filter_upwards [haffine, hgerm] with z hz hf
    simpa [hz, hb0, hg0, SameFiber] using hf
  have hleft : AnalyticOnNhd ℂ (fun z => N tau * D z) univ :=
    fun z _ => analyticAt_const.mul (hD z trivial)
  have hright : AnalyticOnNhd ℂ (fun z => N z * D tau) univ :=
    fun z _ => (hN z trivial).mul analyticAt_const
  have hglobal := hleft.eq_of_eventuallyEq hright hconst
  have hl := (hD tau trivial).differentiableAt.hasDerivAt.const_mul (N tau)
  have hr := (hN tau trivial).differentiableAt.hasDerivAt.mul_const (D tau)
  have hw : N tau * deriv D tau = deriv N tau * D tau :=
    hl.deriv.symm.trans ((congrArg (fun f : ℂ → ℂ => deriv f tau) hglobal).trans hr.deriv)
  apply hdert
  rw [((hN tau trivial).differentiableAt.hasDerivAt.fun_div
    (hD tau trivial).differentiableAt.hasDerivAt hDt).deriv, ← hw, sub_self, zero_div]

/-- Closed discrete differences of the origin fiber force the explicit nonzero projective period.
The hypotheses are checked on the original entire pair, not on an assumed affine inverse. -/
theorem nonzero_period_of_discrete_fiber {N D : ℂ → ℂ} {lam tau : ℂ}
    (hN : AnalyticOnNhd ℂ N univ) (hD : AnalyticOnNhd ℂ D univ)
    (hpair : ∀ z, N z ≠ 0 ∨ D z ≠ 0)
    (hD0 : D 0 ≠ 0) (hDt : D tau ≠ 0)
    (hder0 : deriv (fun z => N z / D z) 0 ≠ 0)
    (hdert : deriv (fun z => N z / D z) tau ≠ 0)
    (hlam : lam ≠ 0) (htau : tau ≠ 0)
    (hlim : Tendsto (fun n : ℕ => (lam ^ n)⁻¹) atTop (𝓝 0))
    (hscale : ∀ x y, SameFiber N D x y → SameFiber N D (lam * x) (lam * y))
    (hreturn : SameFiber N D tau 0)
    (hclosed : IsClosed (fiberDifferences N D)) (hdiscrete : IsDiscrete (fiberDifferences N D)) :
    (lam - 1) * tau ≠ 0 ∧ ∀ z, SameFiber N D (z + (lam - 1) * tau) z := by
  have hne : lam ≠ 1 := by
    intro h
    subst lam
    simp at hlim
  obtain ⟨g, b, hb, hg0, hgd, hgerm⟩ := exists_deck_germ hN hD hD0 hDt hreturn hder0 hdert
  exact ⟨mul_ne_zero (sub_ne_zero.mpr hne) htau,
    period_of_deck_germ hN hD hpair hlam htau hb hlim hscale hreturn hclosed hdiscrete hg0 hgd hgerm⟩

theorem denom_ne_of_sameFiber {N D : ℂ → ℂ} {x y : ℂ}
    (hpair : N x ≠ 0 ∨ D x ≠ 0) (hy : D y ≠ 0) (hxy : SameFiber N D x y) : D x ≠ 0 := by
  intro hx
  have hNx := hpair.resolve_right (not_not.mpr hx)
  have h : N x * D y = 0 := by simpa [SameFiber, hx] using hxy
  exact (mul_ne_zero hNx hy) h

theorem quotient_deriv_ne {N D : ℂ → ℂ} {z : ℂ}
    (hN : AnalyticAt ℂ N z) (hD : AnalyticAt ℂ D z) (hDz : D z ≠ 0)
    (hW : deriv N z * D z - N z * deriv D z ≠ 0) :
    deriv (fun w => N w / D w) z ≠ 0 := by
  rw [(hN.differentiableAt.hasDerivAt.fun_div hD.differentiableAt.hasDerivAt hDz).deriv]
  exact div_ne_zero hW (pow_ne_zero 2 hDz)

theorem sameFiber_swap {N D : ℂ → ℂ} {x y : ℂ} :
    SameFiber D N x y ↔ SameFiber N D x y := by
  dsimp [SameFiber]
  constructor <;> intro h <;> linear_combination -h

theorem fiberDifferences_swap (N D : ℂ → ℂ) : fiberDifferences D N = fiberDifferences N D := by
  ext u
  simp only [fiberDifferences, mem_setOf_eq, sameFiber_swap]

/-- The coordinate-free form for an entire homogeneous pair. Only the nonzero return is assumed
regular; regularity at the origin is deduced. Their common value may be infinity. -/
theorem nonzero_projective_period {N D : ℂ → ℂ} {lam tau : ℂ}
    (hN : AnalyticOnNhd ℂ N univ) (hD : AnalyticOnNhd ℂ D univ)
    (hpair : ∀ z, N z ≠ 0 ∨ D z ≠ 0)
    (hWt : deriv N tau * D tau - N tau * deriv D tau ≠ 0)
    (hlam : lam ≠ 0) (htau : tau ≠ 0)
    (hlim : Tendsto (fun n : ℕ => (lam ^ n)⁻¹) atTop (𝓝 0))
    (hscale : ∀ x y, SameFiber N D x y → SameFiber N D (lam * x) (lam * y))
    (hreturn : SameFiber N D tau 0)
    (hclosed : IsClosed (fiberDifferences N D)) (hdiscrete : IsDiscrete (fiberDifferences N D)) :
    (lam - 1) * tau ≠ 0 ∧ ∀ z, SameFiber N D (z + (lam - 1) * tau) z := by
  by_cases hD0 : D 0 ≠ 0
  · have hDt := denom_ne_of_sameFiber (hpair tau) hD0 hreturn
    have hdert := quotient_deriv_ne (hN tau trivial) (hD tau trivial) hDt hWt
    have hder0 := origin_deriv_ne hN hD hpair hD0 hDt hdert hlam htau hlim hscale hreturn
      hclosed hdiscrete
    exact nonzero_period_of_discrete_fiber hN hD hpair hD0 hDt
      hder0 hdert
      hlam htau hlim hscale hreturn hclosed hdiscrete
  · have hN0 : N 0 ≠ 0 := (hpair 0).resolve_right hD0
    have hpair' : ∀ z, D z ≠ 0 ∨ N z ≠ 0 := fun z => (hpair z).symm
    have hreturn' : SameFiber D N tau 0 := sameFiber_swap.mpr hreturn
    have hNt := denom_ne_of_sameFiber (hpair' tau) hN0 hreturn'
    have hWt' : deriv D tau * N tau - D tau * deriv N tau ≠ 0 := by
      intro h
      apply hWt
      linear_combination -h
    have hscale' : ∀ x y, SameFiber D N x y → SameFiber D N (lam * x) (lam * y) :=
      fun x y hxy => sameFiber_swap.mpr (hscale x y (sameFiber_swap.mp hxy))
    have hc' : IsClosed (fiberDifferences D N) := by rwa [fiberDifferences_swap]
    have hd' : IsDiscrete (fiberDifferences D N) := by rwa [fiberDifferences_swap]
    have hdert := quotient_deriv_ne (hD tau trivial) (hN tau trivial) hNt hWt'
    have hder0 := origin_deriv_ne hD hN hpair' hN0 hNt hdert hlam htau hlim hscale' hreturn' hc' hd'
    obtain ⟨hne, hp⟩ := nonzero_period_of_discrete_fiber hD hN hpair' hN0 hNt
      hder0 hdert
      hlam htau hlim hscale' hreturn' hc' hd'
    exact ⟨hne, fun z => sameFiber_swap.mp (hp z)⟩

/-- The lattice-fiber specialization eliminates the topological premises from the inputs. -/
theorem nonzero_period_of_integer_fiber {N D : ℂ → ℂ} {lam tau : ℂ}
    (hN : AnalyticOnNhd ℂ N univ) (hD : AnalyticOnNhd ℂ D univ)
    (hpair : ∀ z, N z ≠ 0 ∨ D z ≠ 0)
    (hWt : deriv N tau * D tau - N tau * deriv D tau ≠ 0)
    (hlam : lam ≠ 0) (htau : tau ≠ 0)
    (hlim : Tendsto (fun n : ℕ => (lam ^ n)⁻¹) atTop (𝓝 0))
    (hscale : ∀ x y, SameFiber N D x y → SameFiber N D (lam * x) (lam * y))
    (hreturn : SameFiber N D tau 0)
    (hinteger : ∀ z, SameFiber N D z 0 → ∃ k : ℤ, z = k) :
    (lam - 1) * tau ≠ 0 ∧ ∀ z, SameFiber N D (z + (lam - 1) * tau) z := by
  have hsub : fiberDifferences N D ⊆ Set.range ((↑) : ℤ → ℂ) := by
    rintro u ⟨x, y, hx, hy, rfl⟩
    obtain ⟨k, rfl⟩ := hinteger x hx
    obtain ⟨l, rfl⟩ := hinteger y hy
    exact ⟨k - l, by simp⟩
  have hd : IsDiscrete (Set.range ((↑) : ℤ → ℂ)) :=
    Complex.isClosedEmbedding_intCast.isEmbedding.isInducing.isDiscrete_range
  exact nonzero_projective_period hN hD hpair hWt hlam htau hlim hscale hreturn
    (isClosed_of_subset_discrete_closed hsub hd Complex.isClosed_range_intCast) (hd.mono hsub)

end GaloisForLFunctions.HTGeometry.DiscreteFiberDilationPeriod
