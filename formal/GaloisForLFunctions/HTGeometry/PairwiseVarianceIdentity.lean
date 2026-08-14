import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# The pairwise variance identity for infinite weighted families

For a summable nonnegative weight `a` and a slope `τ` whose first two weighted moments converge,

`∑_{(q,r)} a_q a_r (τ_q - τ_r)² = 2 [ (∑ a) (∑ a τ²) - (∑ a τ)² ]`.

Every ordered pair contributes, so an unordered pair contributes twice; extracting a family of
distinct unordered pairs from the nonnegative double sum therefore bounds the Hilbert dispersion
from below.  This is the infinite form of the classical Lagrange identity.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
/-- The double family of pairwise dispersions is summable. -/
theorem summable_pairwise_dispersion {a τ : ι → ℝ}
    (hA : Summable a) (h1 : Summable fun i => a i * τ i)
    (h2 : Summable fun i => a i * τ i ^ 2) (ha : ∀ i, 0 ≤ a i) :
    Summable fun p : ι × ι => a p.1 * a p.2 * (τ p.1 - τ p.2) ^ 2 := by
  have hnormA : Summable fun i => ‖a i‖ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (ha _)] using hA
  have hnorm1 : Summable fun i => ‖a i * τ i‖ := by
    simpa [Real.norm_eq_abs] using h1.abs
  have hnorm2 : Summable fun i => ‖a i * τ i ^ 2‖ := by
    simpa [Real.norm_eq_abs] using h2.abs
  have hs1 : Summable fun p : ι × ι => (a p.1 * τ p.1 ^ 2) * a p.2 :=
    summable_mul_of_summable_norm hnorm2 hnormA
  have hs2 : Summable fun p : ι × ι => (a p.1 * τ p.1) * (a p.2 * τ p.2) :=
    summable_mul_of_summable_norm hnorm1 hnorm1
  have hs3 : Summable fun p : ι × ι => a p.1 * (a p.2 * τ p.2 ^ 2) :=
    summable_mul_of_summable_norm hnormA hnorm2
  have hcongr : ∀ p : ι × ι, a p.1 * a p.2 * (τ p.1 - τ p.2) ^ 2
      = (a p.1 * τ p.1 ^ 2) * a p.2 - 2 * ((a p.1 * τ p.1) * (a p.2 * τ p.2))
        + a p.1 * (a p.2 * τ p.2 ^ 2) := by
    intro p
    ring
  exact ((hs1.sub (hs2.mul_left 2)).add hs3).congr fun p => (hcongr p).symm

set_option maxHeartbeats 1000000 in
/-- **The pairwise variance identity.** -/
theorem tsum_pairwise_dispersion {a τ : ι → ℝ}
    (hA : Summable a) (h1 : Summable fun i => a i * τ i)
    (h2 : Summable fun i => a i * τ i ^ 2) (ha : ∀ i, 0 ≤ a i) :
    (∑' p : ι × ι, a p.1 * a p.2 * (τ p.1 - τ p.2) ^ 2)
      = 2 * ((∑' i, a i) * (∑' i, a i * τ i ^ 2) - (∑' i, a i * τ i) ^ 2) := by
  have hnormA : Summable fun i => ‖a i‖ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (ha _)] using hA
  have hnorm1 : Summable fun i => ‖a i * τ i‖ := by
    simpa [Real.norm_eq_abs] using h1.abs
  have hnorm2 : Summable fun i => ‖a i * τ i ^ 2‖ := by
    simpa [Real.norm_eq_abs] using h2.abs
  have hs1 : Summable fun p : ι × ι => (a p.1 * τ p.1 ^ 2) * a p.2 :=
    summable_mul_of_summable_norm hnorm2 hnormA
  have hs2 : Summable fun p : ι × ι => (a p.1 * τ p.1) * (a p.2 * τ p.2) :=
    summable_mul_of_summable_norm hnorm1 hnorm1
  have hs3 : Summable fun p : ι × ι => a p.1 * (a p.2 * τ p.2 ^ 2) :=
    summable_mul_of_summable_norm hnormA hnorm2
  have hcongr : ∀ p : ι × ι, a p.1 * a p.2 * (τ p.1 - τ p.2) ^ 2
      = (a p.1 * τ p.1 ^ 2) * a p.2 - 2 * ((a p.1 * τ p.1) * (a p.2 * τ p.2))
        + a p.1 * (a p.2 * τ p.2 ^ 2) := by
    intro p
    ring
  rw [tsum_congr hcongr,
    Summable.tsum_add (hs1.sub (hs2.mul_left 2)) hs3,
    Summable.tsum_sub hs1 (hs2.mul_left 2), tsum_mul_left,
    ← tsum_mul_tsum_of_summable_norm hnorm2 hnormA,
    ← tsum_mul_tsum_of_summable_norm hnorm1 hnorm1,
    ← tsum_mul_tsum_of_summable_norm hnormA hnorm2]
  ring

set_option maxHeartbeats 1000000 in
/-- **Anchor extraction.**  The pairs joining a fixed anchor to a set of other indices are
extracted from the nonnegative double sum, so their total is at most the Hilbert dispersion. -/
theorem tsum_anchor_pairs_le {a τ : ι → ℝ}
    (hA : Summable a) (h1 : Summable fun i => a i * τ i)
    (h2 : Summable fun i => a i * τ i ^ 2) (ha : ∀ i, 0 ≤ a i)
    (r : ι) {S : Set ι} (hr : r ∉ S)
    (hSsum : Summable fun q : S => a q * a r * (τ q - τ r) ^ 2) :
    (∑' q : S, a q * a r * (τ q - τ r) ^ 2)
      ≤ (∑' i, a i) * (∑' i, a i * τ i ^ 2) - (∑' i, a i * τ i) ^ 2 := by
  classical
  set g : ι × ι → ℝ := fun p => a p.1 * a p.2 * (τ p.1 - τ p.2) ^ 2 with hgdef
  have hgsum : Summable g := summable_pairwise_dispersion hA h1 h2 ha
  have hgnn : ∀ p, 0 ≤ g p := fun p => by
    rw [hgdef]
    have := ha p.1
    have := ha p.2
    positivity
  set t : S → ℝ := fun q => a q * a r * (τ q - τ r) ^ 2 with htdef
  have htnn : ∀ q : S, 0 ≤ t q := fun q => by
    rw [htdef]
    have := ha q
    have := ha r
    positivity
  set f : S × Bool → ℝ := fun x => t x.1 with hfdef
  have hfnn : ∀ x : S × Bool, 0 ≤ f x := fun x => htnn x.1
  set e : S × Bool → ι × ι := fun x => if x.2 then ((x.1 : ι), r) else (r, (x.1 : ι)) with hedef
  have hinj : Function.Injective e := by
    rintro ⟨q1, b1⟩ ⟨q2, b2⟩ hq
    have hq' : (if b1 then ((q1 : ι), r) else (r, (q1 : ι)))
        = (if b2 then ((q2 : ι), r) else (r, (q2 : ι))) := hq
    cases b1 <;> cases b2 <;>
      simp only [Bool.false_eq_true, if_false, if_true, Prod.mk.injEq] at hq'
    · have : (q1 : ι) = (q2 : ι) := hq'.2
      simp [Subtype.ext this]
    · exact absurd (show r ∈ S by rw [hq'.1]; exact q2.2) hr
    · exact absurd (show r ∈ S by rw [← hq'.1]; exact q1.2) hr
    · have : (q1 : ι) = (q2 : ι) := hq'.1
      simp [Subtype.ext this]
  have hle : ∀ x : S × Bool, f x ≤ g (e x) := by
    rintro ⟨q, b⟩
    cases b
    · show t q ≤ g (r, (q : ι))
      have hval : g (r, (q : ι)) = a q * a r * (τ q - τ r) ^ 2 := by
        rw [hgdef]
        show a r * a q * (τ r - τ q) ^ 2 = a q * a r * (τ q - τ r) ^ 2
        ring
      rw [hval, htdef]
    · show t q ≤ g ((q : ι), r)
      rw [hgdef, htdef]
  have hbool : ∀ q : S, (∑' b : Bool, f (q, b)) = 2 * t q := by
    intro q
    rw [tsum_fintype]
    simp [hfdef]
  have hfsum : Summable f := by
    rw [summable_prod_of_nonneg hfnn]
    refine ⟨fun q => Summable.of_finite, ?_⟩
    refine (hSsum.mul_left 2).congr fun q => ?_
    rw [hbool q, htdef]
  have hmain := Summable.tsum_le_tsum_of_inj e hinj (fun c _ => hgnn c) hle hfsum hgsum
  have hprod : (∑' x : S × Bool, f x) = 2 * ∑' q : S, t q := by
    rw [Summable.tsum_prod' hfsum (fun q => Summable.of_finite), ← tsum_mul_left]
    exact tsum_congr hbool
  have hdouble := tsum_pairwise_dispersion hA h1 h2 ha
  rw [hprod] at hmain
  rw [hdouble] at hmain
  linarith

end GaloisForLFunctions.HTGeometry
