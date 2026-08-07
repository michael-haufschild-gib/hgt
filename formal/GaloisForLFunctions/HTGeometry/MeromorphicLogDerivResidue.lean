import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# The local argument principle

The residue of the logarithmic derivative of a meromorphic germ is its order.  Writing
`f = (z - a)^n · g` with `g` analytic and nonvanishing at `a`, the logarithmic derivative splits as
`n/(z - a)` plus the logarithmic derivative of `g`, which is analytic at `a` and therefore has no
principal part.  The residue of `n/(z - a)` is `n`.

This is the local form of the argument principle.  Mathlib has no complex residue at all, so the
statement is phrased through the Laurent transform of the corpus.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-- The residue of a simple pole with constant numerator. -/
theorem laurentCoeff_const_div_sub (a c : ℂ) :
    laurentCoeff (fun z => c / (z - a)) a (-1) = c := by
  have hshift : laurentShift (fun z => c / (z - a)) a 2 = fun t : ℂ => c * t := by
    funext t
    simp only [laurentShift]
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · rw [show a + t - a = t from by ring]
      field_simp
  have hanalytic : AnalyticAt ℂ (laurentShift (fun z => c / (z - a)) a 2) 0 := by
    rw [hshift]
    fun_prop
  rw [laurentCoeff_eq_taylorCoeffZero hanalytic (by norm_num), hshift]
  have hidx : ((-1 : ℤ) + (2 : ℕ)).toNat = 1 := by norm_num
  rw [hidx, taylorCoeffZero]
  have hderiv : iteratedDeriv 1 (fun t : ℂ => c * t) 0 = c := by
    rw [iteratedDeriv_one]
    simp
  rw [hderiv]
  norm_num

/-- Two functions agreeing off a point have the same logarithmic derivative off that point. -/
theorem logDeriv_eventuallyEq_of_nhdsNE {f h : ℂ → ℂ} {a : ℂ} (hfh : f =ᶠ[𝓝[≠] a] h) :
    logDeriv f =ᶠ[𝓝[≠] a] logDeriv h := by
  obtain ⟨U, hUopen, haU, hU⟩ := mem_nhdsWithin.mp hfh
  have hWmem : U ∩ ({a}ᶜ : Set ℂ) ∈ 𝓝[≠] a := by
    rw [Set.inter_comm]
    exact inter_mem_nhdsWithin _ (hUopen.mem_nhds haU)
  filter_upwards [hWmem] with z hz
  have hWopen : IsOpen (U ∩ ({a}ᶜ : Set ℂ)) := hUopen.inter isOpen_compl_singleton
  have hnhds : U ∩ ({a}ᶜ : Set ℂ) ∈ 𝓝 z := hWopen.mem_nhds hz
  have hlocal : f =ᶠ[𝓝 z] h := by
    filter_upwards [hnhds] with y hy
    exact hU hy
  rw [logDeriv_apply, logDeriv_apply, hlocal.deriv_eq, hlocal.eq_of_nhds]

/-- The logarithmic derivative of the monomial `(z - a)^n`. -/
theorem logDeriv_sub_zpow {a : ℂ} (n : ℤ) {z : ℂ} (hz : z ≠ a) :
    logDeriv (fun w : ℂ => (w - a) ^ n) z = (n : ℂ) / (z - a) := by
  have hsub : z - a ≠ 0 := sub_ne_zero_of_ne hz
  have hdg : DifferentiableAt ℂ (fun w : ℂ => w - a) z := by fun_prop
  have hdf : DifferentiableAt ℂ (fun w : ℂ => w ^ n) ((fun w : ℂ => w - a) z) :=
    differentiableAt_zpow.mpr (Or.inl hsub)
  have hcomp := logDeriv_comp (f := fun w : ℂ => w ^ n) (g := fun w : ℂ => w - a) (x := z) hdf hdg
  have hderiv : deriv (fun w : ℂ => w - a) z = 1 := by
    simp
  simp only [Function.comp_def] at hcomp
  rw [hcomp, hderiv, mul_one, logDeriv_zpow]

/-- **The local argument principle.**  The residue of the logarithmic derivative of a meromorphic
germ of finite order is that order. -/
theorem laurentCoeff_logDeriv_eq_order {f : ℂ → ℂ} {a : ℂ} {n : ℤ}
    (hf : MeromorphicAt f a) (hord : meromorphicOrderAt f a = n) :
    laurentCoeff (logDeriv f) a (-1) = (n : ℂ) := by
  obtain ⟨g, hg, hga, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hord
  -- the model function
  set h : ℂ → ℂ := fun z => (z - a) ^ n * g z with hhdef
  have hfh : f =ᶠ[𝓝[≠] a] h := by
    filter_upwards [hfg] with z hz
    simpa [hhdef] using hz
  -- its logarithmic derivative splits
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
  have hlog : logDeriv f =ᶠ[𝓝[≠] a] fun z => (n : ℂ) / (z - a) + logDeriv g z :=
    (logDeriv_eventuallyEq_of_nhdsNE hfh).trans hsplit
  -- the model has the announced residue
  have hloggAn : AnalyticAt ℂ (logDeriv g) a := by
    have : AnalyticAt ℂ (fun z => deriv g z / g z) a := (hg.deriv).div hg hga
    exact this
  have hmodelMero : MeromorphicAt (fun z => (n : ℂ) / (z - a) + logDeriv g z) a := by
    refine MeromorphicAt.add ?_ hloggAn.meromorphicAt
    exact (analyticAt_const.meromorphicAt).div (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - a) a
      ).meromorphicAt
  rw [← laurentCoeff_congr hmodelMero hlog.symm (-1)]
  rw [laurentCoeff_add (by
        exact (analyticAt_const.meromorphicAt).div
          ((by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - a) a).meromorphicAt))
      hloggAn.meromorphicAt (-1),
    laurentCoeff_const_div_sub a (n : ℂ),
    laurentCoeff_eq_zero_of_analyticAt hloggAn (by norm_num), add_zero]

end GaloisForLFunctions.HTGeometry
