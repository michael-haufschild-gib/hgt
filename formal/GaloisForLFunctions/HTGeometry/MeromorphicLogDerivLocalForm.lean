import GaloisForLFunctions.HTGeometry.MeromorphicLogDerivResidue

/-!
# The logarithmic derivative has at worst a simple pole

Writing a meromorphic germ of finite order `n` as `(z - a)^n · g` with `g` analytic and nonvanishing
at `a`, its logarithmic derivative is `n/(z - a)` plus the logarithmic derivative of `g`, which is
analytic at `a`.  Beyond the residue this says that the whole principal part of `logDeriv f` is the
single simple term: every Laurent coefficient of index `≤ -2` vanishes.

* `exists_analyticAt_logDeriv_local_form` — the local splitting, isolated from the residue theorem;
* `laurentCoeff_const_div_sub_eq_zero` — a constant simple pole has no deeper coefficients;
* `laurentCoeff_logDeriv_eq_zero_of_le` — hence neither does a logarithmic derivative.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-- **The local form of a logarithmic derivative.**  Off the point, `logDeriv f` is a simple polar
term with residue the order, plus a germ analytic at the point. -/
theorem exists_analyticAt_logDeriv_local_form {f : ℂ → ℂ} {a : ℂ} {n : ℤ}
    (hf : MeromorphicAt f a) (hord : meromorphicOrderAt f a = n) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧
      logDeriv f =ᶠ[𝓝[≠] a] fun z => (n : ℂ) / (z - a) + h z := by
  obtain ⟨g, hg, hga, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hord
  set h : ℂ → ℂ := fun z => (z - a) ^ n * g z with hhdef
  have hfh : f =ᶠ[𝓝[≠] a] h := by
    filter_upwards [hfg] with z hz
    simpa [hhdef] using hz
  have hgnear : ∀ᶠ z in 𝓝 a, g z ≠ 0 := hg.continuousAt.eventually_ne hga
  have hsplit : logDeriv h =ᶠ[𝓝[≠] a] fun z => (n : ℂ) / (z - a) + logDeriv g z := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hgnear,
      nhdsWithin_le_nhds hg.eventually_analyticAt] with z hz hgz hgz2
    have hzne : z ≠ a := hz
    have hsub : z - a ≠ 0 := sub_ne_zero_of_ne hzne
    have hzpow : ((z - a) ^ n : ℂ) ≠ 0 := zpow_ne_zero _ hsub
    have hd1 : DifferentiableAt ℂ (fun w : ℂ => (w - a) ^ n) z := by
      have h1 : DifferentiableAt ℂ (fun w : ℂ => w ^ n) (z - a) :=
        differentiableAt_zpow.mpr (Or.inl hsub)
      have h2 : DifferentiableAt ℂ (fun w : ℂ => w - a) z := by fun_prop
      exact h1.comp z h2
    have hd2 : DifferentiableAt ℂ g z := hgz2.differentiableAt
    rw [hhdef, logDeriv_mul z hzpow hgz hd1 hd2, logDeriv_sub_zpow n hzne]
  have hloggAn : AnalyticAt ℂ (logDeriv g) a := by
    have : AnalyticAt ℂ (fun z => deriv g z / g z) a := (hg.deriv).div hg hga
    exact this
  exact ⟨logDeriv g, hloggAn, (logDeriv_eventuallyEq_of_nhdsNE hfh).trans hsplit⟩

/-- A constant simple pole has no Laurent coefficient below index `-1`. -/
theorem laurentCoeff_const_div_sub_eq_zero (a c : ℂ) {ℓ : ℤ} (hℓ : ℓ ≤ -2) :
    laurentCoeff (fun z => c / (z - a)) a ℓ = 0 := by
  obtain ⟨j, hjpos, hj⟩ : ∃ j : ℕ, j ≠ 0 ∧ ℓ + ((j + 1 : ℕ) : ℤ) = 0 :=
    ⟨ℓ.natAbs - 1, by omega, by omega⟩
  have hshift : laurentShift (fun z => c / (z - a)) a (j + 1) = fun t : ℂ => c * t ^ j := by
    funext t
    simp only [laurentShift]
    rcases eq_or_ne t 0 with rfl | ht
    · simp [zero_pow hjpos]
    · rw [show a + t - a = t from by ring, pow_succ]
      field_simp
  have hanalytic : AnalyticAt ℂ (laurentShift (fun z => c / (z - a)) a (j + 1)) 0 := by
    rw [hshift]
    fun_prop
  rw [laurentCoeff_eq_taylorCoeffZero hanalytic (by omega), hshift, hj]
  simp [taylorCoeffZero, zero_pow hjpos]

/-- **The logarithmic derivative has at worst a simple pole.**  Every Laurent coefficient of index
at most `-2` vanishes. -/
theorem laurentCoeff_logDeriv_eq_zero_of_le {f : ℂ → ℂ} {a : ℂ} {n : ℤ}
    (hf : MeromorphicAt f a) (hord : meromorphicOrderAt f a = n) {ℓ : ℤ} (hℓ : ℓ ≤ -2) :
    laurentCoeff (logDeriv f) a ℓ = 0 := by
  obtain ⟨h, hhAn, hlog⟩ := exists_analyticAt_logDeriv_local_form hf hord
  have hpoleMero : MeromorphicAt (fun z : ℂ => (n : ℂ) / (z - a)) a :=
    (analyticAt_const.meromorphicAt).div
      ((by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - a) a).meromorphicAt)
  have hmodelMero : MeromorphicAt (fun z => (n : ℂ) / (z - a) + h z) a :=
    hpoleMero.add hhAn.meromorphicAt
  rw [← laurentCoeff_congr hmodelMero hlog.symm ℓ,
    laurentCoeff_add hpoleMero hhAn.meromorphicAt ℓ,
    laurentCoeff_const_div_sub_eq_zero a (n : ℂ) hℓ,
    laurentCoeff_eq_zero_of_analyticAt hhAn (by omega), add_zero]

end GaloisForLFunctions.HTGeometry
