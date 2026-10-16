import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Analytic cancellation of poles under antidifferentiation

The value of a scaled analytic germ is allowed to vanish. This is essential
when applying the result coordinatewise to a polynomial: a zero coordinate
must not introduce a nonvanishing hypothesis into the continuation theorem.
-/

open Filter Topology

namespace HTGeometry
noncomputable section

/-- Multiplication by the indicated power has an analytic continuation with
the specified value. No assertion of an exact pole is built into this definition. -/
def ScaledAnalyticGerm (f : ℝ → ℝ) (a : ℝ) (k : ℕ) (c : ℝ) : Prop :=
  ∃ g : ℝ → ℝ, AnalyticAt ℝ g a ∧ g a = c ∧
    (fun t => (t - a) ^ k * f t) =ᶠ[𝓝[≠] a] g

theorem ScaledAnalyticGerm.tendsto {f : ℝ → ℝ} {a c : ℝ} {k : ℕ}
    (h : ScaledAnalyticGerm f a k c) :
    Tendsto (fun t => (t - a) ^ k * f t) (𝓝[≠] a) (𝓝 c) := by
  obtain ⟨g, hg, rfl, he⟩ := h
  exact hg.continuousAt.continuousWithinAt.tendsto.congr' he.symm

theorem ScaledAnalyticGerm.unique {f : ℝ → ℝ} {a c d : ℝ} {k : ℕ}
    (hc : ScaledAnalyticGerm f a k c) (hd : ScaledAnalyticGerm f a k d) : c = d :=
  tendsto_nhds_unique hc.tendsto hd.tendsto

theorem ScaledAnalyticGerm.congr {f g : ℝ → ℝ} {a c : ℝ} {k : ℕ}
    (hf : ScaledAnalyticGerm f a k c) (he : f =ᶠ[𝓝[≠] a] g) :
    ScaledAnalyticGerm g a k c := by
  obtain ⟨u, hu, hc, he'⟩ := hf
  refine ⟨u, hu, hc, ?_⟩
  filter_upwards [he, he'] with t ht ht'
  simpa only [ht] using ht'

theorem AnalyticAt.scaledAnalyticGerm {f : ℝ → ℝ} {a : ℝ}
    (hf : AnalyticAt ℝ f a) : ScaledAnalyticGerm f a 0 (f a) :=
  ⟨f, hf, rfl, by simp⟩

theorem ScaledAnalyticGerm.mul {f g : ℝ → ℝ} {a c d : ℝ} {k l : ℕ}
    (hf : ScaledAnalyticGerm f a k c) (hg : ScaledAnalyticGerm g a l d) :
    ScaledAnalyticGerm (fun t => f t * g t) a (k + l) (c * d) := by
  obtain ⟨u, hu, huc, heu⟩ := hf
  obtain ⟨v, hv, hvd, hev⟩ := hg
  refine ⟨fun t => u t * v t, hu.mul hv, by simp only [huc, hvd], ?_⟩
  filter_upwards [heu, hev] with t ht ht'
  rw [← ht, ← ht', pow_add]
  ring

/-- Differentiate a cancelled germ without losing its exact leading value. -/
theorem ScaledAnalyticGerm.deriv {f : ℝ → ℝ} {a c : ℝ} {k : ℕ}
    (hf : MeromorphicAt f a) (h : ScaledAnalyticGerm f a k c) (hk : 0 < k) :
    ScaledAnalyticGerm (deriv f) a (k + 1) (-(k : ℝ) * c) := by
  obtain ⟨g, hg, hgc, he⟩ := h
  refine ⟨fun t => (t - a) * _root_.deriv g t - (k : ℝ) * g t,
    ((analyticAt_id.sub analyticAt_const).mul hg.deriv).sub
      (analyticAt_const.mul hg), by simp [hgc], ?_⟩
  filter_upwards [he, he.nhdsNE_deriv, hf.eventually_analyticAt,
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds]
    with t ht hdt hft hgt
  have hd := (((hasDerivAt_id t).sub_const a).pow k).mul hft.differentiableAt.hasDerivAt
  have hd' : _root_.deriv (fun t => (t - a) ^ k * f t) t =
      (k : ℝ) * (t - a) ^ (k - 1) * f t + (t - a) ^ k * _root_.deriv f t := by
    simpa only [Pi.mul_def, Pi.pow_def, id_eq, mul_one] using hd.deriv
  rw [hd'] at hdt
  have hp : (t - a) ^ (k - 1) * (t - a) = (t - a) ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  calc
    (t - a) ^ (k + 1) * _root_.deriv f t =
        (t - a) * ((k : ℝ) * (t - a) ^ (k - 1) * f t +
          (t - a) ^ k * _root_.deriv f t) -
          (k : ℝ) * ((t - a) ^ (k - 1) * (t - a)) * f t := by rw [pow_succ]; ring
    _ = (t - a) * _root_.deriv g t - (k : ℝ) * g t := by rw [hdt, hp, mul_assoc, ht]

theorem ScaledAnalyticGerm.order_nonneg {f : ℝ → ℝ} {a c : ℝ} {k : ℕ}
    (h : ScaledAnalyticGerm f a k c) :
    0 ≤ meromorphicOrderAt (fun t => (t - a) ^ k * f t) a := by
  obtain ⟨g, hg, _, he⟩ := h
  rw [meromorphicOrderAt_congr he]
  exact hg.meromorphicOrderAt_nonneg

/-- A nonzero cancelled value certifies the exact pole order. -/
theorem ScaledAnalyticGerm.order_eq {f : ℝ → ℝ} {a c : ℝ} {k : ℕ}
    (h : ScaledAnalyticGerm f a k c) (hf : MeromorphicAt f a) (hc : c ≠ 0) :
    meromorphicOrderAt f a = ((-(k : ℤ) : ℤ) : WithTop ℤ) := by
  obtain ⟨g, hg, hgc, he⟩ := h
  rw [meromorphicOrderAt_eq_int_iff hf]
  refine ⟨g, hg, by simpa only [hgc] using hc, ?_⟩
  filter_upwards [he, self_mem_nhdsWithin] with t ht hta
  have hp : (t - a) ^ k ≠ 0 := pow_ne_zero k (sub_ne_zero.mpr hta)
  rw [smul_eq_mul, zpow_neg, zpow_natCast, ← ht, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]

/-- A meromorphic primitive of a pole of order at most `k+1` has order at
most `k`. Its cancelled value is forced, including when that value is zero. -/
theorem scaledAnalyticGerm_of_deriv {f : ℝ → ℝ} {a c : ℝ} {k : ℕ}
    (hf : MeromorphicAt f a) (hk : 0 < k)
    (hd : ScaledAnalyticGerm (deriv f) a (k + 1) c) :
    ScaledAnalyticGerm f a k (-c / k) := by
  have hp : MeromorphicAt (fun t : ℝ => (t - a) ^ k) a := by fun_prop
  have hpd : MeromorphicAt (fun t : ℝ => (t - a) ^ (k + 1)) a := by fun_prop
  have hpow (l : ℕ) : meromorphicOrderAt (fun t : ℝ => (t - a) ^ l) a = (l : ℤ) := by
    simpa only [Pi.pow_def, WithTop.coe_natCast] using
      (meromorphicOrderAt_pow_id_sub_const (𝕜 := ℝ) (x := a) (n := l))
  have hnonneg : 0 ≤ meromorphicOrderAt (fun t => (t - a) ^ k * f t) a := by
    change 0 ≤ meromorphicOrderAt ((fun t => (t - a) ^ k) * f) a
    rw [meromorphicOrderAt_mul hp hf, hpow]
    by_contra hbad
    have hlt : (↑(k : ℤ) : WithTop ℤ) + meromorphicOrderAt f a < 0 :=
      lt_of_not_ge hbad
    have hfinite : meromorphicOrderAt f a ≠ ⊤ := by
      intro he
      simp [he] at hlt
    lift meromorphicOrderAt f a to ℤ using hfinite with m hm
    have hmk : (k : ℤ) + m < 0 := by exact_mod_cast hlt
    have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hder := meromorphicOrderAt_deriv_eq_sub_one hmne hm.symm
    have hdord := hd.order_nonneg
    change 0 ≤ meromorphicOrderAt ((fun t => (t - a) ^ (k + 1)) * deriv f) a at hdord
    rw [meromorphicOrderAt_mul hpd hf.deriv,
      hpow, hder] at hdord
    have hdint : 0 ≤ ((k + 1 : ℕ) : ℤ) + (m - 1) := by exact_mod_cast hdord
    omega
  obtain ⟨g, hg, he⟩ := (hp.mul hf).meromorphicOrderAt_nonneg_iff.mp hnonneg
  have hbase : ScaledAnalyticGerm f a k (g a) := ⟨g, hg, rfl, he⟩
  have hvalue := (hbase.deriv hf hk).unique hd
  have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hevalue : g a = -c / k := by apply (eq_div_iff hkne).mpr; linarith
  simpa only [hevalue] using hbase

/-- The logarithmic derivative has residue equal to the analytic zero order,
including a removable germ when the order is zero. -/
theorem scaledAnalyticGerm_logDeriv {f : ℝ → ℝ} {a : ℝ} {m : ℕ}
    (hf : AnalyticAt ℝ f a) (ho : analyticOrderAt f a = m) :
    ScaledAnalyticGerm (logDeriv f) a 1 m := by
  obtain ⟨g, hg, hgne, he⟩ := hf.analyticOrderAt_eq_natCast.mp ho
  have he' : f =ᶠ[𝓝[≠] a] fun t => (t - a) ^ m * g t := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with t ht
    exact ht
  refine ⟨fun t => (m : ℝ) + (t - a) * (deriv g t / g t),
    analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul
      (hg.deriv.div hg hgne)), by simp, ?_⟩
  filter_upwards [he', he'.nhdsNE_deriv, self_mem_nhdsWithin,
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (hg.continuousAt.eventually_ne hgne).filter_mono nhdsWithin_le_nhds]
    with t ht hdt hta hgt hgn
  have hta' : t - a ≠ 0 := sub_ne_zero.mpr hta
  have hlog : logDeriv f t = logDeriv (fun u => (u - a) ^ m * g u) t := by
    simp only [logDeriv_apply, ht, hdt]
  rw [hlog, logDeriv_mul (f := fun u : ℝ => (u - a) ^ m) (g := g)
    t (pow_ne_zero _ hta') hgn (by fun_prop)
    hgt.differentiableAt, logDeriv_fun_pow (by fun_prop) m]
  have hlin : logDeriv (fun u : ℝ => u - a) t = 1 / (t - a) := by
    rw [logDeriv_apply]
    exact congrArg (fun z : ℝ => z / (t - a)) ((hasDerivAt_id t).sub_const a).deriv
  rw [hlin, logDeriv_apply, pow_one]
  field_simp

/-- The derivative of the logarithmic derivative has a universal cancelled
value. This is the singular connection coefficient in a heat Hankel block. -/
theorem scaledAnalyticGerm_logDeriv_deriv {f : ℝ → ℝ} {a : ℝ} {m : ℕ}
    (hf : AnalyticAt ℝ f a) (ho : analyticOrderAt f a = m) :
    ScaledAnalyticGerm (deriv (logDeriv f)) a 2 (-(m : ℝ)) := by
  have hm : MeromorphicAt (logDeriv f) a := hf.deriv.meromorphicAt.div hf.meromorphicAt
  simpa only [Nat.cast_one, neg_one_mul] using
    (scaledAnalyticGerm_logDeriv hf ho).deriv hm Nat.zero_lt_one

end
end HTGeometry
