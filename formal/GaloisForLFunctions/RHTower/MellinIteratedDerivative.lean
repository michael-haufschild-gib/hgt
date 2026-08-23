import GaloisForLFunctions.RHTower.FriableMomentGammaDerivative

/-!
# The iterated derivative of a Mellin transform

If a density decays faster than every power at infinity and is smaller than every negative power at
the origin, then its Mellin transform is infinitely differentiable on `0 < Re s` and its `t`-th
derivative is the Mellin transform of the density weighted by `(log x)^t`.
-/

open Filter MeasureTheory Set Asymptotics

open scoped Topology

namespace RHTower

noncomputable section

/-- A density with rapid decay at both ends of the positive half-line. -/
structure MellinRapid (f : ℝ → ℂ) : Prop where
  loc : LocallyIntegrableOn f (Ioi (0 : ℝ))
  top : ∀ a : ℝ, f =O[atTop] fun x : ℝ => x ^ (-a)
  bot : ∀ b : ℝ, 0 < b → f =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-b)

/-- The `t`-fold logarithmic weighting of a density. -/
def logWeighted (f : ℝ → ℂ) (t : ℕ) (x : ℝ) : ℂ := ((Real.log x) ^ t : ℝ) • f x

theorem logWeighted_zero (f : ℝ → ℂ) (x : ℝ) : logWeighted f 0 x = f x := by
  rw [logWeighted, pow_zero, one_smul]

theorem log_smul_logWeighted (f : ℝ → ℂ) (t : ℕ) (x : ℝ) :
    Real.log x • logWeighted f t x = logWeighted f (t + 1) x := by
  rw [logWeighted, logWeighted, smul_smul, pow_succ]
  congr 1
  ring

theorem MellinRapid.logWeighted {f : ℝ → ℂ} (hf : MellinRapid f) (t : ℕ) :
    MellinRapid (RHTower.logWeighted f t) := by
  induction t with
  | zero =>
    have hfun : RHTower.logWeighted f 0 = f := funext (logWeighted_zero f)
    rw [hfun]
    exact hf
  | succ t ih =>
    have hfun : RHTower.logWeighted f (t + 1)
        = fun x : ℝ => Real.log x • RHTower.logWeighted f t x :=
      (funext (log_smul_logWeighted f t)).symm
    have hcont : ContinuousOn (fun x : ℝ => Real.log x) (Ioi (0 : ℝ)) :=
      Real.continuousOn_log.mono fun x hx => Set.mem_compl_singleton_iff.mpr (ne_of_gt hx)
    rw [hfun]
    refine ⟨ih.loc.continuousOn_smul isOpen_Ioi.isLocallyClosed hcont, ?_, ?_⟩
    · intro a
      have hlog : (fun x : ℝ => Real.log x) =O[atTop] (fun x : ℝ => x ^ (1 : ℝ)) := by
        have h := isBigO_log_pow_atTop 1
        simpa using h
      refine (hlog.smul (ih.top (a + 1))).trans (IsBigO.of_bound 1 ?_)
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hcollapse : x ^ (1 : ℝ) * x ^ (-(a + 1)) = x ^ (-a) := by
        rw [← Real.rpow_add hx]
        congr 1
        ring
      rw [smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_mul, ← abs_mul, hcollapse]
    · intro b hb
      exact isBigO_rpow_zero_log_smul (a := b / 2) (b := b) (by linarith)
        (ih.bot (b / 2) (by linarith))

theorem hasDerivAt_mellin_logWeighted {f : ℝ → ℂ} (hf : MellinRapid f) (t : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    HasDerivAt (mellin (logWeighted f t)) (mellin (logWeighted f (t + 1)) s) s := by
  have hft := hf.logWeighted t
  have h := mellin_hasDerivAt_of_isBigO_rpow (a := s.re + 1) (b := s.re / 2)
    hft.loc (hft.top (s.re + 1)) (by linarith)
    (hft.bot (s.re / 2) (by linarith)) (by linarith)
  refine h.2.congr_deriv ?_
  congr 1
  funext x
  exact log_smul_logWeighted f t x

/-- **The iterated derivative of a Mellin transform is the log-weighted Mellin transform.** -/
theorem iteratedDeriv_mellin {f : ℝ → ℂ} (hf : MellinRapid f) (t : ℕ) {s : ℂ} (hs : 0 < s.re) :
    iteratedDeriv t (mellin f) s = mellin (logWeighted f t) s := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  induction t generalizing s with
  | zero =>
    rw [iteratedDeriv_zero]
    congr 1
    funext x
    exact (logWeighted_zero f x).symm
  | succ t ih =>
    have hev : iteratedDeriv t (mellin f) =ᶠ[nhds s] mellin (logWeighted f t) := by
      filter_upwards [hopen.mem_nhds hs] with z hz
      exact ih hz
    rw [iteratedDeriv_succ, hev.deriv_eq, (hasDerivAt_mellin_logWeighted hf t hs).deriv]

end

end RHTower
