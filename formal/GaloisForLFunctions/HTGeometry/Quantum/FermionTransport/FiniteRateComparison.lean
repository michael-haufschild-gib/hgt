import GaloisForLFunctions.HTGeometry.BorelSeriesConvolution
import Mathlib.Analysis.Convex.Deriv

/-!
# Taylor bounds for finite nonnegative rate systems

If a field in the unit box has derivative between its incoming rate
sum and that sum minus a uniform loss term, finite Taylor sums bound
the field from both sides. The first nonzero incoming-rate coefficient
then gives the exact leading power at time zero.
-/

open Set Filter
open scoped BigOperators Topology

namespace GaloisForLFunctions.HTGeometry.Quantum.FermiGraph

noncomputable section

variable {V : Type*} [Fintype V]

/-- Apply the incoming-rate matrix to a field. -/
def rateApply (r : V → V → ℝ) (f : V → ℝ) (v : V) : ℝ := ∑ u, r v u * f u

/-- Apply the incoming-rate matrix repeatedly. -/
def ratePower (r : V → V → ℝ) (f : V → ℝ) : ℕ → V → ℝ
  | 0 => f
  | n + 1 => rateApply r (ratePower r f n)

/-- Taylor terms of degree strictly less than the truncation index. -/
def rateTaylor (r : V → V → ℝ) (f : V → ℝ) (n : ℕ) (t : ℝ) (v : V) : ℝ :=
  ∑ j ∈ Finset.range n, dividedPowerFn j t * ratePower r f j v

theorem ratePower_nonneg (r : V → V → ℝ) (hr : ∀ v u, 0 ≤ r v u) (f : V → ℝ)
    (hf : ∀ v, 0 ≤ f v) (n : ℕ) (v : V) : 0 ≤ ratePower r f n v := by
  induction n generalizing v with
  | zero => exact hf v
  | succ n ih =>
    exact Finset.sum_nonneg fun u _ => mul_nonneg (hr v u) (ih u)

private theorem rateApply_mono (r : V → V → ℝ) (hr : ∀ v u, 0 ≤ r v u) :
    Monotone (rateApply r) := by
  intro f g hfg v
  exact Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hfg u) (hr v u)

private theorem rateApply_scale (r : V → V → ℝ) (a : ℝ) (f : V → ℝ) (v : V) :
    rateApply r (fun u => a * f u) v = a * rateApply r f v := by
  unfold rateApply
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => by ring

private theorem rateApply_add (r : V → V → ℝ) (f g : V → ℝ) (v : V) :
    rateApply r (fun u => f u + g u) v = rateApply r f v + rateApply r g v := by
  simp only [rateApply, mul_add, Finset.sum_add_distrib]

private theorem rateApply_sum {J : Type*} (r : V → V → ℝ) (S : Finset J) (F : J → V → ℝ)
    (v : V) : rateApply r (fun u => ∑ j ∈ S, F j u) v = ∑ j ∈ S, rateApply r (F j) v := by
  unfold rateApply
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

private theorem rateTaylor_empty (r : V → V → ℝ) (f : V → ℝ) (t : ℝ) (v : V) :
    rateTaylor r f 0 t v = 0 := by
  simp only [rateTaylor, Finset.range_zero, Finset.sum_empty]

private theorem rateTaylor_succ_zero (r : V → V → ℝ) (f : V → ℝ) (n : ℕ) (v : V) :
    rateTaylor r f (n + 1) 0 v = f v := by
  unfold rateTaylor
  rw [Finset.sum_range_succ']
  simp only [dividedPowerFn_zero_left, Nat.succ_ne_zero, if_false, zero_mul, Finset.sum_const_zero,
    if_true, one_mul, zero_add, ratePower]

private theorem hasDerivAt_rateTaylor_succ (r : V → V → ℝ) (f : V → ℝ) (n : ℕ) (t : ℝ) (v : V) :
    HasDerivAt (fun s => rateTaylor r f (n + 1) s v) (rateApply r (rateTaylor r f n t) v) t := by
  have hfun : (fun s => rateTaylor r f (n + 1) s v) =
      fun s => (∑ j ∈ Finset.range n, dividedPowerFn (j + 1) s * ratePower r f (j + 1) v) + f v := by
    funext s
    unfold rateTaylor
    rw [Finset.sum_range_succ']
    simp only [ratePower, dividedPowerFn, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
  have hr : rateApply r (rateTaylor r f n t) v =
      ∑ j ∈ Finset.range n, dividedPowerFn j t * ratePower r f (j + 1) v := by
    unfold rateTaylor
    rw [rateApply_sum]
    exact Finset.sum_congr rfl fun j _ => rateApply_scale r _ _ _
  have hsum : HasDerivAt (fun s =>
      ∑ j ∈ Finset.range n, dividedPowerFn (j + 1) s * ratePower r f (j + 1) v)
      (∑ j ∈ Finset.range n, dividedPowerFn j t * ratePower r f (j + 1) v) t :=
    HasDerivAt.fun_sum fun j _ => (hasDerivAt_dividedPowerFn_succ j t).mul_const _
  rw [hfun, hr]
  exact hsum.add_const (f v)

private def upperTaylor (r : V → V → ℝ) (f : V → ℝ) (n : ℕ) (t : ℝ) (v : V) : ℝ :=
  rateTaylor r f n t v + dividedPowerFn n t * ratePower r (fun _ => 1) n v

private theorem hasDerivAt_upperTaylor_succ (r : V → V → ℝ) (f : V → ℝ)
    (n : ℕ) (t : ℝ) (v : V) :
    HasDerivAt (fun s => upperTaylor r f (n + 1) s v) (rateApply r (upperTaylor r f n t) v) t := by
  have he : rateApply r (upperTaylor r f n t) v =
      rateApply r (rateTaylor r f n t) v + dividedPowerFn n t * ratePower r (fun _ => 1) (n + 1) v := by
    unfold upperTaylor
    rw [rateApply_add, rateApply_scale]
    rfl
  rw [he]
  exact (hasDerivAt_rateTaylor_succ r f n t v).add
    ((hasDerivAt_dividedPowerFn_succ n t).mul_const _)

private theorem le_of_forward_deriv_le {f g df dg : ℝ → ℝ}
    (hf : ∀ s : ℝ, 0 ≤ s → HasDerivAt f (df s) s)
    (hg : ∀ s : ℝ, 0 ≤ s → HasDerivAt g (dg s) s)
    (hd : ∀ s : ℝ, 0 ≤ s → df s ≤ dg s) (h₀ : f 0 ≤ g 0) {t : ℝ} (ht : 0 ≤ t) :
    f t ≤ g t := by
  have hder (s : ℝ) (hs : 0 ≤ s) : HasDerivAt (fun u => g u - f u) (dg s - df s) s :=
    (hg s hs).sub (hf s hs)
  have hmono : MonotoneOn (fun s => g s - f s) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun s hs => (hder s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hder s (interior_subset hs)).differentiableAt.differentiableWithinAt) ?_
    intro s hs
    rw [(hder s (interior_subset hs)).deriv]
    exact sub_nonneg.mpr (hd s (interior_subset hs))
  have he := hmono (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr ht) ht
  change g 0 - f 0 ≤ g t - f t at he
  linarith only [he, h₀]

/-- Incoming rates and a uniform loss bound give a lower Taylor
truncation and an upper Taylor truncation with an explicit remainder. -/
theorem rateTaylor_bounds (r : V → V → ℝ) (hr : ∀ v u, 0 ≤ r v u) (c : ℝ)
    {z dz : ℝ → V → ℝ}
    (hd : ∀ t : ℝ, 0 ≤ t → ∀ v : V, HasDerivAt (fun s => z s v) (dz t v) t)
    (hbox : ∀ t : ℝ, 0 ≤ t → ∀ v : V, z t v ∈ Icc 0 1)
    (hlo : ∀ t : ℝ, 0 ≤ t → ∀ v : V, rateApply r (z t) v ≤ dz t v + c * z t v)
    (hhi : ∀ t : ℝ, 0 ≤ t → ∀ v : V, dz t v ≤ rateApply r (z t) v)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (v : V) :
    Real.exp (-(c * t)) * rateTaylor r (z 0) n t v ≤ z t v ∧
      z t v ≤ rateTaylor r (z 0) n t v + dividedPowerFn n t * ratePower r (fun _ => 1) n v := by
  let y (s : ℝ) (u : V) := Real.exp (c * s) * z s u
  let dy (s : ℝ) (u : V) := Real.exp (c * s) * (dz s u + c * z s u)
  have hy (s : ℝ) (hs : 0 ≤ s) (u : V) : HasDerivAt (fun a => y a u) (dy s u) s := by
    have he : HasDerivAt (fun a : ℝ => Real.exp (c * a)) (Real.exp (c * s) * c) s := by
      simpa only [id_eq, mul_one] using (((hasDerivAt_id s).const_mul c).exp)
    have hprod := he.mul (hd s hs u)
    have heq : Real.exp (c * s) * c * z s u + Real.exp (c * s) * dz s u = dy s u := by
      dsimp only [dy]
      ring
    rw [heq] at hprod
    exact hprod
  have hyl (s : ℝ) (hs : 0 ≤ s) (u : V) : rateApply r (y s) u ≤ dy s u := by
    dsimp only [y, dy]
    rw [rateApply_scale]
    exact mul_le_mul_of_nonneg_left (hlo s hs u) (Real.exp_pos _).le
  have hm := rateApply_mono r hr
  have lower (j : ℕ) : ∀ s : ℝ, 0 ≤ s → rateTaylor r (z 0) j s ≤ y s := by
    induction j with
    | zero =>
      intro s hs u
      rw [rateTaylor_empty]
      exact mul_nonneg (Real.exp_pos _).le (hbox s hs u).1
    | succ j ih =>
      intro s hs u
      exact le_of_forward_deriv_le (fun a _ => hasDerivAt_rateTaylor_succ r (z 0) j a u)
        (fun a ha => hy a ha u) (fun a ha => (hm (ih a ha) u).trans (hyl a ha u))
        (by rw [rateTaylor_succ_zero]; simp only [y, mul_zero, Real.exp_zero, one_mul, le_refl]) hs
  have upper (j : ℕ) : ∀ s : ℝ, 0 ≤ s → z s ≤ upperTaylor r (z 0) j s := by
    induction j with
    | zero =>
      intro s hs u
      simpa only [upperTaylor, rateTaylor_empty, dividedPowerFn, pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, ratePower, mul_one, zero_add] using (hbox s hs u).2
    | succ j ih =>
      intro s hs u
      exact le_of_forward_deriv_le (fun a ha => hd a ha u)
        (fun a _ => hasDerivAt_upperTaylor_succ r (z 0) j a u)
        (fun a ha => (hhi a ha u).trans (hm (ih a ha) u))
        (by simp only [upperTaylor, rateTaylor_succ_zero, dividedPowerFn_zero_left,
          Nat.succ_ne_zero, if_false, zero_mul, add_zero, le_refl]) hs
  refine ⟨?_, upper n t ht v⟩
  have hscaled := mul_le_mul_of_nonneg_left (lower n t ht v) (Real.exp_pos (-(c * t))).le
  dsimp only [y] at hscaled
  rwa [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at hscaled

/-- If lower-degree Taylor coefficients vanish at a vertex, the
two bounds identify the exact first possible small-time coefficient. -/
theorem tendsto_div_pow_of_rateTaylor_bounds (r : V → V → ℝ) (f : V → ℝ)
    (c : ℝ) (z : ℝ → ℝ) (n : ℕ) (v : V)
    (hzero : ∀ j < n, ratePower r f j v = 0)
    (hb : ∀ t : ℝ, 0 ≤ t →
      Real.exp (-(c * t)) * rateTaylor r f (n + 1) t v ≤ z t ∧
        z t ≤ rateTaylor r f (n + 1) t v + dividedPowerFn (n + 1) t * ratePower r (fun _ => 1) (n + 1) v) :
    Tendsto (fun t : ℝ => z t / t ^ n) (𝓝[>] 0) (𝓝 (ratePower r f n v / (n.factorial : ℝ))) := by
  let A := ratePower r f n v / (n.factorial : ℝ)
  let B := ratePower r (fun _ => 1) (n + 1) v / ((n + 1).factorial : ℝ)
  have heq (t : ℝ) : rateTaylor r f (n + 1) t v = t ^ n * A := by
    unfold rateTaylor
    rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun j hj => by
      rw [hzero j (Finset.mem_range.mp hj), mul_zero]), zero_add, dividedPowerFn]
    dsimp only [A]
    ring
  have hr (t : ℝ) : dividedPowerFn (n + 1) t * ratePower r (fun _ => 1) (n + 1) v =
      t ^ n * (t * B) := by
    unfold dividedPowerFn
    rw [pow_succ]
    dsimp only [B]
    ring
  have hpt (t : ℝ) (ht : 0 < t) :
      Real.exp (-(c * t)) * A ≤ z t / t ^ n ∧ z t / t ^ n ≤ A + t * B := by
    obtain ⟨hlo, hhi⟩ := hb t ht.le
    rw [heq] at hlo hhi
    rw [hr] at hhi
    have hpow : 0 < t ^ n := pow_pos ht _
    constructor
    · exact (le_div_iff₀ hpow).mpr (by
        rw [mul_right_comm (Real.exp (-(c * t))) A (t ^ n), mul_assoc]
        exact hlo)
    · exact (div_le_iff₀ hpow).mpr (by
        rw [mul_comm (A + t * B), mul_add]
        exact hhi)
  have hl : ContinuousAt (fun t : ℝ => Real.exp (-(c * t)) * A) 0 := by fun_prop
  have hu : ContinuousAt (fun t : ℝ => A + t * B) 0 := by fun_prop
  have hl' : Tendsto (fun t : ℝ => Real.exp (-(c * t)) * A) (𝓝[>] 0) (𝓝 A) := by
    simpa only [mul_zero, neg_zero, Real.exp_zero, one_mul] using hl.tendsto.mono_left nhdsWithin_le_nhds
  have hu' : Tendsto (fun t : ℝ => A + t * B) (𝓝[>] 0) (𝓝 A) := by
    simpa only [zero_mul, add_zero] using hu.tendsto.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl' hu' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hpt t ht).1
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hpt t ht).2

#print axioms ratePower_nonneg
#print axioms rateTaylor_bounds
#print axioms tendsto_div_pow_of_rateTaylor_bounds

end

end GaloisForLFunctions.HTGeometry.Quantum.FermiGraph
