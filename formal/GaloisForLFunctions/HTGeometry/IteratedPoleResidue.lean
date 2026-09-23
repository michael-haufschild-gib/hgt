import GaloisForLFunctions.HTGeometry.MovingCanonicalPoleResidue
import GaloisForLFunctions.HTGeometry.EliminationOrderDescent

/-!
# Iterated derivatives of a simple pole

The `m`-th derivative of a simple pole is a pole of order `m + 1` with an explicit factorial
coefficient.  Multiplying by the displacement to that power leaves exactly the coefficient, which is
the leading blow-up value of the `m`-th jet.

Everything else in a germ with a simple pole is analytic, and analyticity is inherited by every
iterated derivative, so the analytic part contributes nothing in the limit.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Every iterated derivative of an analytic germ is analytic. -/
theorem analyticAt_iteratedDeriv' {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x) (m : ℕ) :
    AnalyticAt ℂ (iteratedDeriv m f) x := by
  induction m with
  | zero => simpa [iteratedDeriv_zero] using hf
  | succ m ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

/-- **The iterated derivative of a simple pole.** -/
theorem iteratedDeriv_inv_sub (ζ : ℂ) (m : ℕ) {w : ℂ} (hw : w ≠ ζ) :
    iteratedDeriv m (fun x : ℂ => (x - ζ)⁻¹) w
      = (-1) ^ m * (m.factorial : ℂ) / (w - ζ) ^ (m + 1) := by
  induction m generalizing w with
  | zero =>
      have hne : w - ζ ≠ 0 := sub_ne_zero.mpr hw
      simp [iteratedDeriv_zero]
  | succ m ih =>
      have hne : w - ζ ≠ 0 := sub_ne_zero.mpr hw
      have hpow : (w - ζ) ^ (m + 1) ≠ 0 := pow_ne_zero _ hne
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv m (fun x : ℂ => (x - ζ)⁻¹)
          =ᶠ[𝓝 w] fun x => (-1) ^ m * (m.factorial : ℂ) / (x - ζ) ^ (m + 1) :=
        Filter.eventuallyEq_of_mem (isOpen_ne.mem_nhds hw) fun x hx => ih hx
      rw [hev.deriv_eq]
      have hbase : HasDerivAt (fun x : ℂ => (x - ζ) ^ (m + 1))
          (((m : ℂ) + 1) * (w - ζ) ^ m) w := by
        have h1 : HasDerivAt (fun x : ℂ => x - ζ) 1 w := (hasDerivAt_id w).sub_const ζ
        have h2 : HasDerivAt (fun x : ℂ => (x - ζ) ^ (m + 1))
            (((m + 1 : ℕ) : ℂ) * (w - ζ) ^ (m + 1 - 1) * 1) w := h1.pow (m + 1)
        simpa using h2
      have hinv : HasDerivAt (fun x : ℂ => ((x - ζ) ^ (m + 1))⁻¹)
          (-(((m : ℂ) + 1) * (w - ζ) ^ m) / ((w - ζ) ^ (m + 1)) ^ (2 : ℕ)) w := hbase.inv hpow
      have hmul := hinv.const_mul ((-1 : ℂ) ^ m * (m.factorial : ℂ))
      have hfun : (fun x : ℂ => (-1 : ℂ) ^ m * (m.factorial : ℂ) / (x - ζ) ^ (m + 1))
          = fun x : ℂ => (-1 : ℂ) ^ m * (m.factorial : ℂ) * ((x - ζ) ^ (m + 1))⁻¹ := by
        funext x
        rw [div_eq_mul_inv]
      rw [hfun, hmul.deriv, Nat.factorial_succ]
      push_cast
      field_simp
      ring


/-! ## The jets of the moving canonical log-derivative -/

set_option maxHeartbeats 1000000 in
/-- **The leading blow-up value of every jet.**  The `m`-th derivative of the log-derivative blows up
at order `m + 1` with leading value `-(-1)^m m!`, the same at every zero. -/
theorem tendsto_iteratedDeriv_movingCanonicalLogDerivative_mul_pow
    (θ : BoundedRealSequence) (n m : ℕ) {u : ℕ → ℂ}
    (hupper : ∀ j, 0 < (u j).im)
    (hu : Tendsto u atTop (𝓝 ((movingCanonicalZero θ n : ℂ)))) :
    Tendsto (fun j => iteratedDeriv m (movingCanonicalLogDerivative θ) (u j) *
      (u j - (movingCanonicalZero θ n : ℂ)) ^ (m + 1)) atTop
      (𝓝 (-((-1) ^ m * (m.factorial : ℂ)))) := by
  set ζ : ℂ := (movingCanonicalZero θ n : ℂ) with hζ
  have hζim : ζ.im = 0 := by rw [hζ]; simp
  have hune : ∀ j, u j ≠ ζ := by
    intro j hcon
    have : (u j).im = 0 := by rw [hcon, hζim]
    exact absurd this (ne_of_gt (hupper j))
  have hM : AnalyticAt ℂ (movingCanonicalProduct θ) ζ :=
    movingCanonicalProduct_analytic θ ζ (Set.mem_univ ζ)
  obtain ⟨g, hg, hg0, hev⟩ :=
    (hM.analyticOrderAt_eq_natCast (n := 1)).mp
      (movingCanonicalProduct_zero_analyticOrderAt θ n)
  have hU : ∀ᶠ z in 𝓝 ζ,
      movingCanonicalProduct θ z = (z - ζ) * g z ∧ g z ≠ 0 ∧ AnalyticAt ℂ g z := by
    filter_upwards [hev, hg.continuousAt.eventually_ne hg0, hg.eventually_analyticAt]
      with z h1 h2 h3
    exact ⟨by rw [h1, pow_one, smul_eq_mul], h2, h3⟩
  obtain ⟨U, hUsub, hUopen, hUmem⟩ := eventually_nhds_iff.mp hU
  set k : ℂ → ℂ := fun w => -(deriv g w / g w) with hk
  have hkA : ∀ z ∈ U, AnalyticAt ℂ k z := by
    intro z hz
    obtain ⟨-, hgz, hganz⟩ := hUsub z hz
    exact ((hganz.deriv.div hganz hgz).neg)
  have hpole : ∀ z ∈ U, z ≠ ζ → movingCanonicalLogDerivative θ z
      = (fun x : ℂ => -(x - ζ)⁻¹) z + k z := by
    intro z hz hzζ
    obtain ⟨hfac, hgz, hganz⟩ := hUsub z hz
    have hzζ' : z - ζ ≠ 0 := sub_ne_zero.mpr hzζ
    have hMz : movingCanonicalProduct θ z ≠ 0 := by
      rw [hfac]
      exact mul_ne_zero hzζ' hgz
    have hzne : ∀ p, z ≠ (movingCanonicalZero θ p : ℂ) := by
      intro p hcon
      exact hMz ((movingCanonicalProduct_eq_zero_iff θ z).mpr ⟨p, hcon⟩)
    have hderiv : deriv (movingCanonicalProduct θ) z = g z + (z - ζ) * deriv g z := by
      have hfacev : movingCanonicalProduct θ =ᶠ[𝓝 z] fun w => (w - ζ) * g w :=
        Filter.eventuallyEq_of_mem (hUopen.mem_nhds hz) fun w hw => (hUsub w hw).1
      have hd1 : HasDerivAt (fun w : ℂ => w - ζ) 1 z := (hasDerivAt_id z).sub_const ζ
      have hd2 : HasDerivAt g (deriv g z) z := hganz.differentiableAt.hasDerivAt
      have hprod : HasDerivAt (fun w : ℂ => (w - ζ) * g w)
          (1 * g z + (z - ζ) * deriv g z) z := hd1.mul hd2
      rw [hfacev.deriv_eq, hprod.deriv]
      ring
    have hlog := neg_logDeriv_movingCanonicalProduct_eq θ hzne
    rw [← hlog, logDeriv_apply, hderiv, hfac, hk]
    field_simp
    ring
  have hitd : ∀ z ∈ U, z ≠ ζ →
      iteratedDeriv m (movingCanonicalLogDerivative θ) z
        = iteratedDeriv m (fun x : ℂ => -(x - ζ)⁻¹) z + iteratedDeriv m k z := by
    intro z hz hzζ
    have hV : IsOpen (U ∩ {x : ℂ | x ≠ ζ}) := hUopen.inter isOpen_ne
    have hzV : z ∈ U ∩ {x : ℂ | x ≠ ζ} := ⟨hz, hzζ⟩
    have hevz : movingCanonicalLogDerivative θ
        =ᶠ[𝓝 z] (fun x : ℂ => -(x - ζ)⁻¹) + k :=
      Filter.eventuallyEq_of_mem (hV.mem_nhds hzV) fun w hw => hpole w hw.1 hw.2
    rw [hevz.iteratedDeriv_eq]
    refine iteratedDeriv_add ?_ ((hkA z hz).contDiffAt)
    have hbase : AnalyticAt ℂ (fun x : ℂ => x - ζ) z :=
      analyticAt_id.sub analyticAt_const
    exact ((hbase.inv (sub_ne_zero.mpr hzζ)).neg).contDiffAt
  have hval : ∀ z ∈ U, z ≠ ζ →
      iteratedDeriv m (movingCanonicalLogDerivative θ) z * (z - ζ) ^ (m + 1)
        = -((-1) ^ m * (m.factorial : ℂ)) + iteratedDeriv m k z * (z - ζ) ^ (m + 1) := by
    intro z hz hzζ
    have hzζ' : z - ζ ≠ 0 := sub_ne_zero.mpr hzζ
    rw [hitd z hz hzζ, add_mul]
    congr 1
    have hneg : (fun x : ℂ => -(x - ζ)⁻¹) = -(fun x : ℂ => (x - ζ)⁻¹) := by
      funext x
      simp
    rw [hneg, iteratedDeriv_neg, iteratedDeriv_inv_sub ζ m hzζ]
    field_simp
  have hev2 : ∀ᶠ j in atTop,
      iteratedDeriv m (movingCanonicalLogDerivative θ) (u j) * (u j - ζ) ^ (m + 1)
        = -((-1) ^ m * (m.factorial : ℂ)) + iteratedDeriv m k (u j) * (u j - ζ) ^ (m + 1) := by
    filter_upwards [hu (hUopen.mem_nhds hUmem)] with j hj
    exact hval (u j) hj (hune j)
  have hsub : Tendsto (fun j => (u j - ζ) ^ (m + 1)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun j => u j - ζ) atTop (𝓝 0) := by
      have := hu.sub (tendsto_const_nhds (x := ζ))
      simpa using this
    have := h0.pow (m + 1)
    rwa [zero_pow (Nat.succ_ne_zero m)] at this
  have hkc : Tendsto (fun j => iteratedDeriv m k (u j)) atTop (𝓝 (iteratedDeriv m k ζ)) :=
    (analyticAt_iteratedDeriv' (hkA ζ hUmem) m).continuousAt.tendsto.comp hu
  have hlim : Tendsto (fun j =>
      -((-1) ^ m * (m.factorial : ℂ)) + iteratedDeriv m k (u j) * (u j - ζ) ^ (m + 1)) atTop
      (𝓝 (-((-1) ^ m * (m.factorial : ℂ)) + iteratedDeriv m k ζ * 0)) :=
    (tendsto_const_nhds).add (hkc.mul hsub)
  rw [mul_zero, add_zero] at hlim
  exact Filter.Tendsto.congr' (hev2.mono fun j h => h.symm) hlim


/-! ## Translated jets -/

/-- **A translated jet blows up at the translated zero, with the same leading value.** -/
theorem tendsto_iteratedDeriv_translate_movingCanonicalLogDerivative
    (θ : BoundedRealSequence) (n m : ℕ) (σ : ℂ) {u : ℕ → ℂ}
    (hupper : ∀ j, 0 < (u j + σ).im)
    (hu : Tendsto u atTop (𝓝 ((movingCanonicalZero θ n : ℂ) - σ))) :
    Tendsto (fun j => iteratedDeriv m (movingCanonicalLogDerivative θ) (u j + σ) *
      (u j - ((movingCanonicalZero θ n : ℂ) - σ)) ^ (m + 1)) atTop
      (𝓝 (-((-1) ^ m * (m.factorial : ℂ)))) := by
  have hu' : Tendsto (fun j => u j + σ) atTop (𝓝 ((movingCanonicalZero θ n : ℂ))) := by
    have h := hu.add (tendsto_const_nhds (x := σ))
    simpa using h
  have hbase := tendsto_iteratedDeriv_movingCanonicalLogDerivative_mul_pow θ n m hupper hu'
  refine hbase.congr fun j => ?_
  congr 1
  ring

theorem jetLeadingValue_ne_zero (m : ℕ) : -((-1 : ℂ) ^ m * (m.factorial : ℂ)) ≠ 0 := by
  refine neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ ?_) ?_)
  · exact neg_ne_zero.mpr one_ne_zero
  · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)

/-- **The blow-up datum of a translated jet, in the form the valuation machinery consumes.**  The
scale is the displacement from the translated zero, the order is `m + 1`, and the leading value is
`-(-1)^m m!` — independent of which zero is approached. -/
theorem gradedAlong_translate_jet (θ : BoundedRealSequence) (n m : ℕ) (σ : ℂ) {u : ℕ → ℂ}
    (hupper : ∀ j, 0 < (u j + σ).im)
    (hu : Tendsto u atTop (𝓝 ((movingCanonicalZero θ n : ℂ) - σ))) :
    GradedAlong (fun w => iteratedDeriv m (movingCanonicalLogDerivative θ) (w + σ)) u
      (fun j => u j - ((movingCanonicalZero θ n : ℂ) - σ)) (m + 1)
      (-((-1) ^ m * (m.factorial : ℂ))) :=
  ⟨jetLeadingValue_ne_zero m,
    tendsto_iteratedDeriv_translate_movingCanonicalLogDerivative θ n m σ hupper hu⟩

end GaloisForLFunctions.HTGeometry
