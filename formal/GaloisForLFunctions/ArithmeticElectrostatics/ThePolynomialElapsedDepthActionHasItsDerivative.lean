import GaloisForLFunctions.ArithmeticElectrostatics.ThePolynomialHeatZerosHaveTheirReciprocalVelocity
import GaloisForLFunctions.ArithmeticElectrostatics.ThePolynomialHeatCollisionsAreFinite
import GaloisForLFunctions.ArithmeticElectrostatics.TheConjugatePacketPaysElapsedHeat
import GaloisForLFunctions.ArithmeticElectrostatics.ThePolynomialElapsedDepthActionIsContinuous
import GaloisForLFunctions.ArithmeticElectrostatics.ThePolynomialHeatClockComposes
import GaloisForLFunctions.HTGeometry.RiemannGaussian.FiniteRealRootDecomposition
import GaloisForLFunctions.HTGeometry.ForwardRegularIntervalComparison

/-!
# Polynomial elapsed-depth velocity and the initial comparison

At a simple heat fibre, implicit-function branches remain distinct and
exhaust the roots because heat preserves degree. Their exact reciprocal
velocities differentiate the corrected action. Conjugation pairs the full
derivative into the upper-packet inequality.

For an initially separable real polynomial, only finitely many fibres fail
to be simple. Freezing the final nonreal count gives a continuous comparison
through those fibres and down to time zero, proving the initial moment bound.
-/

open Polynomial Complex Filter Topology Set Metric
open GaloisForLFunctions.ZeroConfigurationGeometry
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

/-- Simple heat roots admit differentiable branches that enumerate every nearby fibre. -/
theorem exists_polynomial_heat_root_enumeration {p : ℂ[X]} (hp : p ≠ 0)
    {t : ℝ} (hs : (heatFlow (t : ℂ) p).Separable) :
    ∃ g : ((heatFlow (t : ℂ) p).roots.toFinset) → ℝ → ℂ,
      (∀ a, g a t = (a : ℂ)) ∧
      (∀ a, HasDerivAt (g a)
        ((heatFlow (t : ℂ) p).derivative.derivative.eval (a : ℂ) /
          (heatFlow (t : ℂ) p).derivative.eval (a : ℂ)) t) ∧
      ∀ᶠ s : ℝ in 𝓝 t, (heatFlow (s : ℂ) p).roots =
        ((heatFlow (t : ℂ) p).roots.toFinset.attach.val.map
          (fun a => g a s)) := by
  classical
  let S := (heatFlow (t : ℂ) p).roots.toFinset
  have hz (a : S) : (heatFlow (t : ℂ) p).eval (a : ℂ) = 0 :=
    (mem_roots (heatFlow_degree_ne_zero hp (t : ℂ)).2).mp
      (Multiset.mem_toFinset.mp a.property)
  have hsimple (a : S) : (heatFlow (t : ℂ) p).derivative.eval (a : ℂ) ≠ 0 := by
    simpa only [eval₂_id] using hs.eval₂_derivative_ne_zero (RingHom.id ℂ) (hz a)
  choose g hg0 hgd hgroot using fun a : S =>
    exists_polynomial_heat_zero_branch p (hz a) (hsimple a)
  refine ⟨g, hg0, hgd, ?_⟩
  have hpair (a b : S) : ∀ᶠ s in 𝓝 t, g a s = g b s → a = b := by
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall fun _ _ => hab
    have hne : g a t ≠ g b t := by
      rw [hg0, hg0]
      exact fun he => hab (Subtype.ext he)
    have he := ((hgd a).continuousAt.dist (hgd b).continuousAt).eventually
      (Ioi_mem_nhds (dist_pos.mpr hne))
    filter_upwards [he] with s hs' heq
    have : (0 : ℝ) < 0 := by simpa only [heq, dist_self] using hs'
    exact (lt_irrefl _ this).elim
  have hall := Filter.eventually_all.mpr fun a => Filter.eventually_all.mpr (hpair a)
  have hroots := Filter.eventually_all.mpr hgroot
  filter_upwards [hall, hroots] with s hsi hsr
  let L := S.attach.val.map (fun a => g a s)
  have hinj : Function.Injective (fun a : S => g a s) := fun a b he => hsi a b he
  have hLn : L.Nodup := Multiset.Nodup.map hinj S.attach.nodup
  have hle : L ≤ (heatFlow (s : ℂ) p).roots := by
    apply (Multiset.le_iff_subset hLn).mpr
    intro z hz'
    obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hz'
    exact (mem_roots (heatFlow_degree_ne_zero hp (s : ℂ)).2).mpr (hsr a)
  have hcard : L.card = (heatFlow (s : ℂ) p).roots.card := by
    simp only [L, Multiset.card_map, Finset.card_val, Finset.card_attach,
      S, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs),
      IsAlgClosed.card_roots_eq_natDegree, (heatFlow_degree_ne_zero hp (s : ℂ)).1,
      (heatFlow_degree_ne_zero hp (t : ℂ)).1]
  exact (Multiset.eq_of_le_of_card_le hle hcard.ge).symm

#print axioms exists_polynomial_heat_root_enumeration

/-- Corrected elapsed-depth rate at a polynomial heat root. -/
def polynomialElapsedDepthRate (p : ℂ[X]) (q t : ℝ) (a : ℂ) : ℝ :=
  2 * q * ((a.im ^ 2 + 2 * t) ^ (q - 1) - (2 * t) ^ (q - 1)) +
    elapsedDepthWeight q (2 * t) a.im *
      ((heatFlow (t : ℂ) p).derivative.derivative.eval a /
        (heatFlow (t : ℂ) p).derivative.eval a).im

private theorem corrected_polynomial_depth_hasDerivAt
    {y : ℝ → ℝ} {v t q : ℝ} (ht : 0 < t) (hy : HasDerivAt y v t) :
    HasDerivAt (fun s => (y s ^ 2 + 2 * s) ^ q - (2 * s) ^ q)
      (2 * q * ((y t ^ 2 + 2 * t) ^ (q - 1) - (2 * t) ^ (q - 1)) +
        elapsedDepthWeight q (2 * t) (y t) * v) t := by
  have htime := (hasDerivAt_id t).const_mul 2
  have hb : y t ^ 2 + 2 * t ≠ 0 := by positivity
  have hc : 2 * t ≠ 0 := by positivity
  have hd := (((hy.pow 2).add htime).rpow_const (Or.inl hb) (p := q)).sub
    (htime.rpow_const (Or.inl hc) (p := q))
  simp only [Pi.add_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat,
    Nat.reduceSub, pow_one, mul_one] at hd
  apply hd.congr_deriv
  unfold elapsedDepthWeight
  ring

/-- The corrected action differentiates by summing the actual simple-root velocities. -/
theorem polynomialElapsedDepthAction_hasDerivAt_of_separable
    {p : ℂ[X]} (hp : p ≠ 0) {t : ℝ} (ht : 0 < t)
    (hs : (heatFlow (t : ℂ) p).Separable) (q : ℝ) :
    HasDerivAt (polynomialElapsedDepthAction p q)
      (∑ a ∈ (heatFlow (t : ℂ) p).roots.toFinset, polynomialElapsedDepthRate p q t a) t := by
  classical
  let S := (heatFlow (t : ℂ) p).roots.toFinset
  obtain ⟨g, hg0, hgd, hroot⟩ := exists_polynomial_heat_root_enumeration hp hs
  have hd (a : S) : HasDerivAt
      (fun s => ((g a s).im ^ 2 + 2 * s) ^ q - (2 * s) ^ q)
      (polynomialElapsedDepthRate p q t a) t := by
    have him : HasDerivAt (fun s => (g a s).im)
        ((heatFlow (t : ℂ) p).derivative.derivative.eval (a : ℂ) /
          (heatFlow (t : ℂ) p).derivative.eval (a : ℂ)).im t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hgd a)
    simpa only [polynomialElapsedDepthRate, hg0] using
      corrected_polynomial_depth_hasDerivAt (q := q) ht him
  have hds := HasDerivAt.sum (u := S.attach) (fun a _ => hd a)
  have heq : polynomialElapsedDepthAction p q =ᶠ[𝓝 t]
      (fun s => ∑ a ∈ S.attach, (((g a s).im ^ 2 + 2 * s) ^ q - (2 * s) ^ q)) := by
    filter_upwards [hroot] with s hs'
    unfold polynomialElapsedDepthAction
    rw [hs', Multiset.map_map, Finset.sum_eq_multiset_sum]
    rfl
  have hfun : (∑ a ∈ S.attach,
      fun s => ((g a s).im ^ 2 + 2 * s) ^ q - (2 * s) ^ q) =
      (fun s => ∑ a ∈ S.attach, (((g a s).im ^ 2 + 2 * s) ^ q - (2 * s) ^ q)) := by
    funext s
    rw [Finset.sum_apply]
  rw [hfun] at hds
  have hder := hds.congr_of_eventuallyEq heq
  rw [Finset.sum_attach S (polynomialElapsedDepthRate p q t)] at hder
  exact hder

#print axioms polynomialElapsedDepthAction_hasDerivAt_of_separable

private theorem eval_realPolynomial_conj (A : ℝ[X]) (z : ℂ) :
    (A.map ofRealHom).eval (starRingEnd ℂ z) =
      starRingEnd ℂ ((A.map ofRealHom).eval z) := by
  simpa only [RiemannGaussian.conjugatePolynomial_real_map, Complex.conj_conj] using
    RiemannGaussian.conjugatePolynomial_eval (A.map ofRealHom) (starRingEnd ℂ z)

private theorem polynomialElapsedDepthRate_conj (p : ℝ[X]) (q t : ℝ) (a : ℂ) :
    polynomialElapsedDepthRate (p.map ofRealHom) q t (starRingEnd ℂ a) =
      polynomialElapsedDepthRate (p.map ofRealHom) q t a := by
  unfold polynomialElapsedDepthRate elapsedDepthWeight
  simp only [heatFlow_ofReal, Polynomial.derivative_map, eval_realPolynomial_conj,
    ← map_div₀, Complex.conj_im, neg_sq]
  ring

private theorem polynomialElapsedDepthRate_real (p : ℂ[X]) (q t : ℝ) {a : ℂ}
    (ha : a.im = 0) : polynomialElapsedDepthRate p q t a = 0 := by
  simp only [polynomialElapsedDepthRate, elapsedDepthWeight, ha, zero_pow two_ne_zero,
    zero_add, sub_self, mul_zero, zero_mul, add_zero]

/-- A conjugation-even weight vanishing on the real axis sums to twice its upper-root sum. -/
theorem sum_realPolynomial_even_roots (A : ℝ[X]) (f : ℂ → ℝ)
    (heven : ∀ z, f (starRingEnd ℂ z) = f z)
    (hreal : ∀ z, z.im = 0 → f z = 0) :
    (((A.map ofRealHom).roots).map f).sum =
      2 * ((RiemannGaussian.realPolynomialUpperRootMultiset A).map f).sum := by
  have hr : ((RiemannGaussian.realPolynomialRealRootMultiset A).map f).sum = 0 := by
    have hm : (RiemannGaussian.realPolynomialRealRootMultiset A).map f =
        (RiemannGaussian.realPolynomialRealRootMultiset A).map (fun _ => (0 : ℝ)) :=
      Multiset.map_congr rfl fun z hz => hreal z
        (RiemannGaussian.realPolynomialRealRootMultiset_im_eq_zero A z hz)
    rw [hm, Multiset.map_const', Multiset.sum_replicate, smul_zero]
  rw [RiemannGaussian.realPolynomial_roots_eq_real_add_conjugatePairs]
  simp only [RiemannGaussian.conjugatePairRootMultiset, Multiset.map_add,
    Multiset.sum_add, Multiset.map_map, Function.comp_apply, heven, hr]
  ring

/-- Each nonreal root pays the baseline derivative in the full packet rate. -/
theorem polynomialElapsedDepthRate_sum_le {p : ℝ[X]} {t : ℝ} (ht : 0 < t)
    (hs : (heatFlow (t : ℂ) (p.map ofRealHom)).Separable) {q : ℝ} (hq : 0 ≤ q) :
    (∑ a ∈ (heatFlow (t : ℂ) (p.map ofRealHom)).roots.toFinset,
      polynomialElapsedDepthRate (p.map ofRealHom) q t a) ≤
      -(2 * q * (2 * t) ^ (q - 1)) * (nonrealRootCount (polyHeat t p) : ℝ) := by
  classical
  let S := (heatFlow (t : ℂ) (p.map ofRealHom)).roots.toFinset
  let U := S.filter (fun z => 0 < z.im)
  have hSv : (heatFlow (t : ℂ) (p.map ofRealHom)).roots = S.val := by
    dsimp only [S]
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr (Polynomial.nodup_roots hs)]
  have hU : RiemannGaussian.realPolynomialUpperRootMultiset (polyHeat t p) = U.val := by
    rw [RiemannGaussian.realPolynomialUpperRootMultiset, ← heatFlow_ofReal, hSv]
    rfl
  have hconj (a : ℂ) (ha : a ∈ S) : starRingEnd ℂ a ∈ S := by
    apply Multiset.mem_toFinset.mpr
    rw [heatFlow_ofReal, ← RiemannGaussian.realPolynomial_roots_map_conj]
    apply Multiset.mem_map.mpr
    refine ⟨a, ?_, rfl⟩
    rw [← heatFlow_ofReal]
    exact Multiset.mem_toFinset.mp ha
  have hcount : nonrealRootCount (polyHeat t p) = 2 * U.card := by
    have hc := RiemannGaussian.realPolynomial_realRoot_card_add_two_mul_upperRoot_card
      (polyHeat t p)
    rw [realPolynomialRealRootMultiset_eq_map_roots,
      Multiset.card_map, hU] at hc
    unfold nonrealRootCount
    change (polyHeat t p).roots.card + 2 * U.card = (polyHeat t p).natDegree at hc
    omega
  have hhalf : (∑ a ∈ S, polynomialElapsedDepthRate (p.map ofRealHom) q t a) =
      2 * ∑ a ∈ U, polynomialElapsedDepthRate (p.map ofRealHom) q t a := by
    have h := sum_realPolynomial_even_roots (polyHeat t p)
      (polynomialElapsedDepthRate (p.map ofRealHom) q t)
      (polynomialElapsedDepthRate_conj p q t)
      (fun a ha => polynomialElapsedDepthRate_real (p.map ofRealHom) q t ha)
    rw [← heatFlow_ofReal, hSv, hU] at h
    exact h
  have hquot (a : ℂ) (ha : a ∈ S) :
      (heatFlow (t : ℂ) (p.map ofRealHom)).derivative.derivative.eval a /
          (heatFlow (t : ℂ) (p.map ofRealHom)).derivative.eval a =
        2 * ∑ b ∈ S, (a - b)⁻¹ := by
    have ham := Multiset.mem_toFinset.mp ha
    have hp' := Polynomial.ne_zero_of_mem_roots ham
    have hz := (mem_roots hp').mp ham
    have hd : (heatFlow (t : ℂ) (p.map ofRealHom)).derivative.eval a ≠ 0 := by
      simpa only [eval₂_id] using hs.eval₂_derivative_ne_zero (RingHom.id ℂ) hz
    exact polynomial_heat_quotient_eq_reciprocal_field (Polynomial.nodup_roots hs) ham hd
  have hupper := elapsedDepth_conjugation_closed_drift_nonpos S hconj hq
    (mul_nonneg zero_le_two ht.le)
  have hsum : (∑ a ∈ U, polynomialElapsedDepthRate (p.map ofRealHom) q t a) =
      (∑ a ∈ U, (2 * q * (a.im ^ 2 + 2 * t) ^ (q - 1) +
        elapsedDepthWeight q (2 * t) a.im * (2 * ∑ b ∈ S, (a - b)⁻¹).im)) -
        (2 * q * (2 * t) ^ (q - 1)) * U.card := by
    calc
      _ = ∑ a ∈ U, ((2 * q * (a.im ^ 2 + 2 * t) ^ (q - 1) +
          elapsedDepthWeight q (2 * t) a.im * (2 * ∑ b ∈ S, (a - b)⁻¹).im) -
          (2 * q * (2 * t) ^ (q - 1))) := by
        apply Finset.sum_congr rfl
        intro a ha
        unfold polynomialElapsedDepthRate
        rw [hquot a (Finset.mem_filter.mp ha).1]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        ring
  change (∑ a ∈ S, polynomialElapsedDepthRate (p.map ofRealHom) q t a) ≤ _
  rw [hhalf, hsum, hcount]
  push_cast
  nlinarith only [hupper]

#print axioms polynomialElapsedDepthRate_sum_le

/-- Initial separability gives the sharp elapsed-depth bound through every later collision. -/
theorem polynomial_elapsed_moment_le_initial_of_separable {p : ℝ[X]} (hp : p ≠ 0)
    (hs : (p.map ofRealHom).Separable) {q b : ℝ} (hq : 0 < q) (hb : 0 ≤ b) :
    polynomialElapsedDepthAction (p.map ofRealHom) q b +
        (2 * b) ^ q * (nonrealRootCount (polyHeat b p) : ℝ) ≤
      ((p.map ofRealHom).roots.map (fun z => (z.im ^ 2) ^ q)).sum := by
  have hpC : p.map ofRealHom ≠ 0 := (Polynomial.map_ne_zero_iff ofRealHom.injective).mpr hp
  have hpowC : Continuous (fun s : ℝ => (2 * s) ^ q) :=
    (continuous_const.mul continuous_id).rpow_const (fun _ => Or.inr hq.le)
  have hc : ContinuousOn
      (fun s => polynomialElapsedDepthAction (p.map ofRealHom) q s +
        (2 * s) ^ q * (nonrealRootCount (polyHeat b p) : ℝ)) (Icc 0 b) :=
    ((continuousOn_polynomialElapsedDepthAction hpC hq.le).mono
      (fun s hs' => hs'.1)).add (hpowC.mul continuous_const).continuousOn
  have h := le_initial_of_forward_intervals_interior hb hc (by
    intro t ht
    obtain ⟨δ, hδ, hreg⟩ := exists_separable_polynomial_heat_forward hpC hs t
    refine ⟨δ, hδ, fun s hs' hsb => ?_⟩
    have hs0 : 0 < s := ht.1.trans hs'.1
    have hD := polynomialElapsedDepthAction_hasDerivAt_of_separable hpC hs0 (hreg s hs') q
    have hbound := polynomialElapsedDepthRate_sum_le hs0 (hreg s hs') hq.le
    have hpow : HasDerivAt (fun s : ℝ => (2 * s) ^ q)
        (2 * q * (2 * s) ^ (q - 1)) s := by
      have hd := ((hasDerivAt_id s).const_mul 2).rpow_const
        (Or.inl (show 2 * s ≠ 0 by positivity)) (p := q)
      simpa only [id_eq, mul_one] using hd
    have hcount : (nonrealRootCount (polyHeat b p) : ℝ) ≤
        (nonrealRootCount (polyHeat s p) : ℝ) := by
      exact_mod_cast antitone_nonrealRootCount_polyHeat hp hsb.le
    have hcoef : 0 ≤ 2 * q * (2 * s) ^ (q - 1) :=
      mul_nonneg (mul_nonneg zero_le_two hq.le) (Real.rpow_nonneg (by positivity) _)
    have hpay := mul_le_mul_of_nonneg_left hcount hcoef
    refine ⟨_, (hD.add (hpow.mul_const (nonrealRootCount (polyHeat b p) : ℝ))).hasDerivWithinAt, ?_⟩
    nlinarith only [hbound, hpay])
  simpa only [polynomialElapsedDepthAction_zero _ hq, mul_zero,
    Real.zero_rpow hq.ne', zero_mul, add_zero] using h

#print axioms polynomial_elapsed_moment_le_initial_of_separable

private theorem sum_corrected_elapsed_add_nonreal_count (S : Multiset ℂ) (q c : ℝ) :
    (S.map (fun z => (z.im ^ 2 + c) ^ q - c ^ q)).sum +
        c ^ q * ((S.filter (fun z => z.im ≠ 0)).card : ℝ) =
      ((S.filter (fun z => z.im ≠ 0)).map (fun z => (z.im ^ 2 + c) ^ q)).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons z S ih =>
    by_cases hz : z.im = 0
    · simpa only [Multiset.map_cons, Multiset.sum_cons, Multiset.filter_cons,
        hz, ne_eq, not_true_eq_false, if_false, zero_pow two_ne_zero,
        zero_add, sub_self] using ih
    · simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.filter_cons,
        hz, ne_eq, not_false_eq_true, if_true, Multiset.map_add, Multiset.sum_add,
        Multiset.map_singleton, Multiset.sum_singleton, Multiset.card_add, Multiset.card_singleton,
        Nat.cast_add, Nat.cast_one]
      linear_combination ih

/-- Full nonreal elapsed-depth moment, with both conjugate halves counted. -/
def polynomialElapsedDepthMoment (p : ℝ[X]) (q t : ℝ) : ℝ :=
  polynomialElapsedDepthAction (p.map ofRealHom) q t +
    (2 * t) ^ q * (nonrealRootCount (polyHeat t p) : ℝ)

/-- Restoring the nonreal baseline recovers exactly the multiplicity-counted moment. -/
theorem polynomialElapsedDepthMoment_eq_sum (p : ℝ[X]) (q t : ℝ) :
    polynomialElapsedDepthMoment p q t =
      ((((polyHeat t p).map ofRealHom).roots.filter (fun z => z.im ≠ 0)).map
        (fun z => (z.im ^ 2 + 2 * t) ^ q)).sum := by
  rw [polynomialElapsedDepthMoment, polynomialElapsedDepthAction,
    nonrealRootCount_eq, heatFlow_ofReal]
  exact sum_corrected_elapsed_add_nonreal_count _ q (2 * t)

#print axioms polynomialElapsedDepthMoment_eq_sum

end
end GaloisForLFunctions.ArithmeticElectrostatics
