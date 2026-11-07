/-
Incoming height profiles adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicCuspBarrier

/-!
# Smooth incoming powers and their compact height defects

A transition times `v^s` equals the incoming power above the transition
interval. Its positive-Laplacian defect has compact height support and
is an entire function of the spectral parameter at each height.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

def logRatioPower (s : ℂ) (v q : ℝ) : ℂ :=
  Complex.exp (s * ((Real.log v - Real.log q : ℝ) : ℂ))

lemma logRatioPower_eq_cpow (s : ℂ) {v q : ℝ} (hv : 0<v) (hq : 0<q) :
    logRatioPower s v q = ((v/q : ℝ):ℂ)^s := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hv hq).ne'),
    ← Complex.ofReal_log (div_pos hv hq).le, Real.log_div hv.ne' hq.ne']
  unfold logRatioPower
  congr 1
  ring

lemma hasDerivAt_logRatioPower (s : ℂ) {f g : ℝ → ℝ} {x f' g' : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (hf0 : f x ≠ 0) (hg0 : g x ≠ 0) :
    HasDerivAt (fun t => logRatioPower s (f t) (g t))
      (logRatioPower s (f x) (g x) * s * ((f'/f x-g'/g x : ℝ):ℂ)) x := by
  convert (((hf.log hf0).sub (hg.log hg0)).ofReal_comp.const_mul s).cexp using 1 <;> try rfl
  all_goals try dsimp [logRatioPower]
  all_goals ring

lemma hasDerivAt_deriv_logRatioPower (s : ℂ) (f g df dg : ℝ → ℝ) (x ddf ddg : ℝ)
    (hf : ∀t, HasDerivAt f (df t) t) (hg : ∀t, HasDerivAt g (dg t) t)
    (hdf : HasDerivAt df ddf x) (hdg : HasDerivAt dg ddg x)
    (hf0 : f x ≠ 0) (hg0 : g x ≠ 0) :
    HasDerivAt (deriv (fun t => logRatioPower s (f t) (g t)))
      (logRatioPower s (f x) (g x) *
        (s^2 * ((df x/f x-dg x/g x : ℝ):ℂ)^2 +
         s * (((ddf*f x-df x*df x)/(f x)^2 -
           (ddg*g x-dg x*dg x)/(g x)^2 : ℝ):ℂ))) x := by
  have hnear : ∀ᶠ t in 𝓝 x, f t ≠ 0 ∧ g t ≠ 0 :=
    ((hf x).continuousAt.eventually_ne hf0).and ((hg x).continuousAt.eventually_ne hg0)
  have heq : (deriv (fun t => logRatioPower s (f t) (g t))) =ᶠ[𝓝 x]
      (fun t => logRatioPower s (f t) (g t) * s * ((df t/f t-dg t/g t : ℝ):ℂ)) := by
    filter_upwards [hnear] with t ht
    exact (hasDerivAt_logRatioPower s (hf t) (hg t) ht.1 ht.2).deriv
  have hfirst := hasDerivAt_logRatioPower s (hf x) (hg x) hf0 hg0
  have hsecond := ((hdf.div (hf x) hf0).sub (hdg.div (hg x) hg0)).ofReal_comp
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert (hfirst.mul_const s).mul hsecond using 1 <;> try rfl
  all_goals try simp only [Pi.sub_apply,Pi.div_apply]
  all_goals ring

def positiveHeightPower (s : ℂ) (v : ℝ) : ℂ := logRatioPower s v 1
lemma positiveHeightPower_eq_cpow (s : ℂ) (v : ℝ) (hv : 0<v) :
    positiveHeightPower s v=(v:ℂ)^s := by
  simpa only [positiveHeightPower,div_one] using logRatioPower_eq_cpow s hv (by norm_num : (0:ℝ)<1)

lemma positiveHeightPower_hasDerivAt (s : ℂ) (v : ℝ) (hv : v≠0) :
    HasDerivAt (positiveHeightPower s) (positiveHeightPower s v*s/(v:ℂ)) v := by
  convert hasDerivAt_logRatioPower s (hasDerivAt_id v) (hasDerivAt_const v (1:ℝ)) hv one_ne_zero using 1 <;> try rfl
  all_goals simp [positiveHeightPower,div_eq_mul_inv]

lemma positiveHeightPower_hasDerivAt_deriv (s : ℂ) (v : ℝ) (hv : v≠0) :
    HasDerivAt (deriv (positiveHeightPower s))
      (positiveHeightPower s v*s*(s-1)/(v:ℂ)^2) v := by
  convert hasDerivAt_deriv_logRatioPower s id (fun _ => 1) (fun _ => 1) (fun _ => 0) v 0 0
    (fun x => hasDerivAt_id x) (fun x => hasDerivAt_const x (1:ℝ))
    (hasDerivAt_const v (1:ℝ)) (hasDerivAt_const v (0:ℝ)) hv one_ne_zero using 1 <;> try rfl
  simp only [id_eq,zero_mul,mul_one,sub_self,sub_zero,one_pow,div_one,
    Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_pow,
    Complex.ofReal_zero,positiveHeightPower]
  field_simp [Complex.ofReal_ne_zero.mpr hv]
  ring

def cuspSeedProfile (a b : ℝ) (s : ℂ) (v : ℝ) : ℂ :=
  (cuspTransition a b v:ℂ)*positiveHeightPower s v

lemma cuspSeedProfile_zero (a b : ℝ) (s : ℂ) (v : ℝ) (hab : a<b) (hv : v≤a) :
    cuspSeedProfile a b s v=0 := by simp [cuspSeedProfile,cuspTransition_zero a b v hab hv]
lemma cuspSeedProfile_incoming (a b : ℝ) (s : ℂ) (v : ℝ)
    (hab : a<b) (hv : b≤v) (hpos : 0<v) : cuspSeedProfile a b s v=(v:ℂ)^s := by
  simp [cuspSeedProfile,cuspTransition_one a b v hab hv,positiveHeightPower_eq_cpow s v hpos]

lemma cuspSeedProfile_hasDerivAt (a b : ℝ) (s : ℂ) (v : ℝ) (hv : v≠0) :
    HasDerivAt (cuspSeedProfile a b s)
      (((deriv (cuspTransition a b) v:ℝ):ℂ)*positiveHeightPower s v+
        (cuspTransition a b v:ℂ)*(positiveHeightPower s v*s/(v:ℂ))) v := by
  exact (((cuspTransition_contDiff a b).differentiable (by simp) v).hasDerivAt.ofReal_comp).mul
    (positiveHeightPower_hasDerivAt s v hv)

lemma cuspSeedProfile_hasDerivAt_deriv (a b : ℝ) (s : ℂ) (v : ℝ) (hv : v≠0) :
    HasDerivAt (deriv (cuspSeedProfile a b s))
      (((deriv (deriv (cuspTransition a b)) v:ℝ):ℂ)*positiveHeightPower s v+
        2*((deriv (cuspTransition a b) v:ℝ):ℂ)*(positiveHeightPower s v*s/(v:ℂ))+
        (cuspTransition a b v:ℂ)*(positiveHeightPower s v*s*(s-1)/(v:ℂ)^2)) v := by
  have hχ := ((cuspTransition_contDiff a b).differentiable (by simp) v).hasDerivAt.ofReal_comp
  have hdχ := (((contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2).differentiable
    (by simp) v).hasDerivAt.ofReal_comp
  have hH := positiveHeightPower_hasDerivAt s v hv
  have hdH := positiveHeightPower_hasDerivAt_deriv s v hv
  have heq : deriv (cuspSeedProfile a b s) =ᶠ[𝓝 v]
      (fun x => ((deriv (cuspTransition a b) x:ℝ):ℂ)*positiveHeightPower s x+
        (cuspTransition a b x:ℂ)*deriv (positiveHeightPower s) x) := by
    filter_upwards [eventually_ne_nhds hv] with x hx
    rw [(cuspSeedProfile_hasDerivAt a b s x hx).deriv,(positiveHeightPower_hasDerivAt s x hx).deriv]
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert (hdχ.mul hH).add (hχ.mul hdH) using 1 <;> try rfl
  rw [hH.deriv]
  ring

def cuspSeedDefectProfile (a b : ℝ) (s : ℂ) (v : ℝ) : ℂ :=
  positiveHeightPower s v*((v:ℂ)^2*((deriv (deriv (cuspTransition a b)) v:ℝ):ℂ)+
    (2*s-1)*(v:ℂ)*((deriv (cuspTransition a b) v:ℝ):ℂ))

lemma cuspSeedProfile_laplace_defect (a b : ℝ) (s : ℂ) (v : ℝ) (hv : v≠0) :
    (v:ℂ)^2*deriv (deriv (cuspSeedProfile a b s)) v-
      (v:ℂ)*deriv (cuspSeedProfile a b s) v-s*(s-2)*cuspSeedProfile a b s v=
        cuspSeedDefectProfile a b s v := by
  rw [(cuspSeedProfile_hasDerivAt a b s v hv).deriv,(cuspSeedProfile_hasDerivAt_deriv a b s v hv).deriv]
  unfold cuspSeedDefectProfile cuspSeedProfile
  field_simp [Complex.ofReal_ne_zero.mpr hv]
  ; ring

lemma cuspSeedDefectProfile_zero (a b : ℝ) (s : ℂ) (v : ℝ) (hab : a<b) (hv : v<a ∨ b<v) :
    cuspSeedDefectProfile a b s v=0 := by
  obtain ⟨h₁,h₂⟩ := cuspTransition_derivatives a b v hab hv
  simp [cuspSeedDefectProfile,h₁,h₂]

lemma cuspSeedDefectProfile_hasCompactSupport (a b : ℝ) (s : ℂ) (hab : a<b) :
    HasCompactSupport (cuspSeedDefectProfile a b s) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro v hv
  by_contra hn
  have hout : v<a ∨ b<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using hn
  exact hv (cuspSeedDefectProfile_zero a b s v hab hout)

lemma positiveHeightPower_contDiffAt (s : ℂ) (v : ℝ) (hv : v≠0) :
    ContDiffAt ℝ ∞ (positiveHeightPower s) v := by
  have hlog : ContDiffAt ℝ ∞ (fun x : ℝ => (Real.log x:ℂ)) v :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp v (Real.contDiffAt_log.mpr hv)
  have hs : ContDiffAt ℝ ∞ (fun x : ℝ => s*(Real.log x:ℂ)) v := contDiffAt_const.mul hlog
  unfold positiveHeightPower logRatioPower
  simpa only [Real.log_one,sub_zero] using hs.cexp

lemma cuspSeedProfile_contDiffAt (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    ContDiffAt ℝ ∞ (cuspSeedProfile a b s) v :=
  (Complex.ofRealCLM.contDiff.contDiffAt.comp v (cuspTransition_contDiff a b).contDiffAt).mul
    (positiveHeightPower_contDiffAt s v hv.ne')

lemma cuspSeedDefectProfile_contDiffAt (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    ContDiffAt ℝ ∞ (cuspSeedDefectProfile a b s) v := by
  have hχ₁ : ContDiff ℝ ∞ (deriv (cuspTransition a b)) :=
    (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2
  have hχ₂ : ContDiff ℝ ∞ (deriv (deriv (cuspTransition a b))) :=
    (contDiff_infty_iff_deriv.mp hχ₁).2
  have hd₁ := Complex.ofRealCLM.contDiff.contDiffAt.comp v hχ₁.contDiffAt
  have hd₂ := Complex.ofRealCLM.contDiff.contDiffAt.comp v hχ₂.contDiffAt
  have hid : ContDiffAt ℝ ∞ (fun x : ℝ => (x:ℂ)) v := Complex.ofRealCLM.contDiff.contDiffAt
  exact (positiveHeightPower_contDiffAt s v hv.ne').mul
    (((hid.pow 2).mul hd₂).add ((contDiffAt_const.mul hid).mul hd₁))

lemma cuspSeedDefectProfile_continuous (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    Continuous (cuspSeedDefectProfile a b s) := by
  rw [continuous_iff_continuousAt]
  intro v
  by_cases hv : v<a
  · have heq : cuspSeedDefectProfile a b s =ᶠ[𝓝 v] (fun _ => (0:ℂ)) := by
      filter_upwards [Iio_mem_nhds hv] with x hx
      exact cuspSeedDefectProfile_zero a b s x hab (Or.inl hx)
    exact continuousAt_const.congr heq.symm
  · exact (cuspSeedDefectProfile_contDiffAt a b s v (lt_of_lt_of_le ha (le_of_not_gt hv))).continuousAt

lemma cuspSeedDefectProfile_integrable (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    Integrable (cuspSeedDefectProfile a b s) volume :=
  (cuspSeedDefectProfile_continuous a b s ha hab).integrable_of_hasCompactSupport
    (cuspSeedDefectProfile_hasCompactSupport a b s hab)

lemma cuspSeedProfile_entire (a b v : ℝ) : Differentiable ℂ (fun s => cuspSeedProfile a b s v) := by
  unfold cuspSeedProfile positiveHeightPower logRatioPower
  fun_prop
lemma cuspSeedDefectProfile_entire (a b v : ℝ) : Differentiable ℂ (fun s => cuspSeedDefectProfile a b s v) := by
  unfold cuspSeedDefectProfile positiveHeightPower logRatioPower
  fun_prop

#print axioms cuspSeedProfile_laplace_defect
#print axioms cuspSeedDefectProfile_hasCompactSupport
#print axioms cuspSeedDefectProfile_entire
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
