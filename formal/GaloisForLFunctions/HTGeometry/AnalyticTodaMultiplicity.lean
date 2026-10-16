import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Data.Sign.Basic

/-!
# Multiplicities forced by the Toda identity

At a zero of order `m > 0`, `f f'' - (f')²` has exact order `2m-2`.
The logarithmic derivative has a simple pole, whose derivative has a
double pole; multiplication by `f²` gives the claimed order without
subtracting two equal-order Taylor expansions.
-/

open Filter Topology

namespace HTGeometry
noncomputable section

/-- Exact order of the curvature numerator at a nonflat analytic zero. -/
theorem meromorphicOrderAt_curvature {f : ℝ → ℝ} {a : ℝ} {m : ℕ}
    (hf : AnalyticAt ℝ f a) (hm : 0 < m) (ho : analyticOrderAt f a = m) :
    meromorphicOrderAt (fun t => f t * deriv (deriv f) t - deriv f t ^ 2) a =
      ((2 * (m : ℤ) - 2 : ℤ) : WithTop ℤ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hod : analyticOrderAt (deriv f) a = k :=
    analyticOrderAt_deriv_of_pos hf (by simpa only [Nat.cast_succ] using ho)
  have hlog : meromorphicOrderAt (logDeriv f) a = ((-1 : ℤ) : WithTop ℤ) := by
    change meromorphicOrderAt (deriv f / f) a = _
    rw [meromorphicOrderAt_div hf.deriv.meromorphicAt hf.meromorphicAt,
      hf.deriv.meromorphicOrderAt_eq, hf.meromorphicOrderAt_eq, hod, ho,
      ENat.map_coe, ENat.map_coe]
    exact_mod_cast (show (k : ℤ) - ((k + 1 : ℕ) : ℤ) = -1 by omega)
  have hlogd : meromorphicOrderAt (deriv (logDeriv f)) a =
      ((-2 : ℤ) : WithTop ℤ) := by
    simpa using meromorphicOrderAt_deriv_eq_sub_one
      (by norm_num : ((-1 : ℤ) : ℝ) ≠ 0) hlog
  have hne : ∀ᶠ t in 𝓝[≠] a, f t ≠ 0 := by
    rcases hf.eventually_eq_zero_or_eventually_ne_zero with hz | hz
    · have ht := analyticOrderAt_eq_top.mpr hz
      rw [ho] at ht
      exact (ENat.coe_ne_top _ ht).elim
    · exact hz
  have he : (fun t => f t * deriv (deriv f) t - deriv f t ^ 2) =ᶠ[𝓝[≠] a]
      (fun t => f t ^ 2 * deriv (logDeriv f) t) := by
    filter_upwards [hf.eventually_analyticAt.filter_mono nhdsWithin_le_nhds, hne]
      with t ht hnt
    change f t * deriv (deriv f) t - deriv f t ^ 2 =
      f t ^ 2 * deriv (deriv f / f) t
    rw [deriv_div ht.deriv.differentiableAt ht.differentiableAt hnt]
    field_simp
  rw [meromorphicOrderAt_congr he]
  change meromorphicOrderAt ((f ^ 2) * deriv (logDeriv f)) a = _
  have hlm : MeromorphicAt (logDeriv f) a := hf.deriv.meromorphicAt.div hf.meromorphicAt
  rw [meromorphicOrderAt_mul (hf.pow 2).meromorphicAt
      hlm.deriv,
    meromorphicOrderAt_pow hf.meromorphicAt, hf.meromorphicOrderAt_eq,
    ho, ENat.map_coe, hlogd]
  change (↑(2 : ℤ) : WithTop ℤ) * ↑(k.succ : ℤ) + ↑(-2 : ℤ) = _
  rw [← WithTop.coe_mul, ← WithTop.coe_add]
  congr 1

/-- Dirichlet endpoints determine every multiplicity in a Toda zero block.
The recurrence has constant second difference `-2`. -/
theorem toda_multiplicity_block (M : ℕ → ℕ) {d : ℕ} (hd : 0 < d)
    (hzero : M 0 = 0) (hend : M d = 0)
    (hrec : ∀ k, k + 2 ≤ d →
      (M k : ℤ) + M (k + 2) = 2 * M (k + 1) - 2) :
    ∀ k ≤ d, M k = k * (d - k) := by
  have hdiff : ∀ k, k + 1 ≤ d →
      (M (k + 1) : ℤ) - M k = M 1 - 2 * (k : ℤ) := by
    intro k
    induction k with
    | zero => simp [hzero]
    | succ k ih =>
        intro hk
        have hprev := ih (by omega)
        have hnext := hrec k (by omega)
        push_cast
        linarith
  have hpoly : ∀ k ≤ d,
      (M k : ℤ) = (k : ℤ) * ((M 1 : ℤ) + 1 - k) := by
    intro k
    induction k with
    | zero => simp [hzero]
    | succ k ih =>
        intro hk
        have hprev := ih (by omega)
        have hnext := hdiff k (by omega)
        push_cast
        nlinarith
  have hboundary := hpoly d le_rfl
  rw [hend, Nat.cast_zero] at hboundary
  have hdne : (d : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hslope : (M 1 : ℤ) + 1 - d = 0 :=
    (mul_eq_zero.mp hboundary.symm).resolve_left hdne
  intro k hk
  have h := hpoly k hk
  have he : (M k : ℤ) = (k : ℤ) * ((d : ℤ) - k) := by nlinarith
  exact_mod_cast (show (M k : ℤ) = ((k * (d - k) : ℕ) : ℤ) by
    simpa only [Nat.cast_mul, Nat.cast_sub hk] using he)

/-- The exact analytic order determines crossing versus tangency. Values
at equal small distances on opposite sides have product sign `(-1)^m`. -/
theorem eventually_reflection_sign_of_analyticOrderAt {f : ℝ → ℝ} {a : ℝ} {m : ℕ}
    (hf : AnalyticAt ℝ f a) (ho : analyticOrderAt f a = m) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      SignType.sign (f (a - t) * f (a + t)) = (-1 : SignType) ^ m := by
  obtain ⟨g, hg, hgne, he⟩ := hf.analyticOrderAt_eq_natCast.mp ho
  have he' : ∀ᶠ t in 𝓝 a, f t = (t - a) ^ m * g t := by
    simpa only [smul_eq_mul] using he
  have hp : Tendsto (fun t : ℝ => a + t) (𝓝 0) (𝓝 a) := by
    simpa only [Pi.add_def, add_zero] using
      (continuousAt_const.add continuousAt_id : ContinuousAt (fun t : ℝ => a + t) 0).tendsto
  have hm : Tendsto (fun t : ℝ => a - t) (𝓝 0) (𝓝 a) := by
    simpa only [Pi.sub_def, sub_zero] using
      (continuousAt_const.sub continuousAt_id : ContinuousAt (fun t : ℝ => a - t) 0).tendsto
  have hprod : Tendsto (fun t : ℝ => g (a - t) * g (a + t))
      (𝓝 0) (𝓝 (g a * g a)) :=
    (hg.continuousAt.tendsto.comp hm).mul (hg.continuousAt.tendsto.comp hp)
  have hpos := hprod.eventually (eventually_gt_nhds (mul_self_pos.mpr hgne))
  filter_upwards [(hm.eventually he').filter_mono nhdsWithin_le_nhds,
    (hp.eventually he').filter_mono nhdsWithin_le_nhds,
    hpos.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t hmt hpt htpos ht
  have htne : t ≠ 0 := ht
  have hm' : a - t - a = -t := by ring
  have hp' : a + t - a = t := by ring
  rw [hmt, hpt, hm', hp']
  have hfactor : (-t) ^ m * g (a - t) * (t ^ m * g (a + t)) =
      (-1 : ℝ) ^ m * ((t ^ m) ^ 2 * (g (a - t) * g (a + t))) := by
    rw [neg_pow]
    ring
  have hpositive : 0 < (t ^ m) ^ 2 * (g (a - t) * g (a + t)) :=
    mul_pos (sq_pos_of_ne_zero (pow_ne_zero m htne)) htpos
  rw [hfactor, sign_mul, sign_pow, sign_pos hpositive,
    sign_neg (neg_one_lt_zero : (-1 : ℝ) < 0), mul_one]

end
end HTGeometry
