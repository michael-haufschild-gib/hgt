import GaloisForLFunctions.RHTower.EulerHellingerDyadicSignSeries
import GaloisForLFunctions.RHTower.EulerActivationSquarefreeProbability
import GaloisForLFunctions.RHTower.GammaSewnSynchronizedEulerFisherBarycenter

/-!
# The cubic confluence current and its Wold/Gamma factorization

The third jet of the reflected Hellinger sewing cost at the lossless boundary is `-12 P_N'''(1)`,
where `P_N` is the finite prime Euler logarithm.  Closing the local third derivative in closed form
turns that jet into an explicit positive prime-power current

```text
L_N'''(0) = 12 ∑_{p < N} (log p)^3 ∑_{k ≥ 1} k^2 p^(-k).
```

Each local factor splits into two independent source objects: the all-positive-depth geometric
Wold activation `q/(1 - q)` at `q = p⁻¹`, and the complete synchronized Gamma half-height second
moment `M_{2,p}` of the same prime ray.  The dyadic normalization forced by the all-orders jet law
is the scalar `48 log p`:

```text
12 (log p)^3 ∑_{k ≥ 1} k^2 p^(-k) = 48 (log p) (q / (1 - q)) M_{2,p}.
```
-/

open Set

namespace RHTower

noncomputable section

/-! ## Closed form of the local Euler-log third jet -/

private theorem exp_node_lt_one {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    Real.exp (-(s * L)) < 1 := by
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by nlinarith)

private theorem one_sub_exp_node_pos {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    0 < 1 - Real.exp (-(s * L)) := by
  have := exp_node_lt_one hL hs
  linarith

private theorem hasDerivAt_expNode (L s : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-(t * L))) (-L * Real.exp (-(s * L))) s := by
  have h0 : HasDerivAt (fun t : ℝ => t * L) L s := by
    simpa using (hasDerivAt_id s).mul_const L
  have h : HasDerivAt (fun t : ℝ => -(t * L)) (-L) s := h0.neg
  rw [show -L * Real.exp (-(s * L)) = Real.exp (-(s * L)) * (-L) by ring]
  exact h.exp

private theorem hasDerivAt_oneSubExpNode (L s : ℝ) :
    HasDerivAt (fun t : ℝ => 1 - Real.exp (-(t * L))) (L * Real.exp (-(s * L))) s := by
  rw [show L * Real.exp (-(s * L)) = -(-L * Real.exp (-(s * L))) by ring]
  exact (hasDerivAt_expNode L s).const_sub (1 : ℝ)

private theorem hasDerivAt_localLog {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => -Real.log (1 - Real.exp (-(t * L))))
      (-(L * Real.exp (-(s * L)) / (1 - Real.exp (-(s * L))))) s := by
  have hne : (1 - Real.exp (-(s * L))) ≠ 0 := ne_of_gt (one_sub_exp_node_pos hL hs)
  exact ((hasDerivAt_oneSubExpNode L s).log hne).neg

private theorem hasDerivAt_localLogD1 {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => -(L * Real.exp (-(t * L)) / (1 - Real.exp (-(t * L)))))
      (L ^ 2 * Real.exp (-(s * L)) / (1 - Real.exp (-(s * L))) ^ 2) s := by
  have hpos := one_sub_exp_node_pos hL hs
  have hne : (1 - Real.exp (-(s * L))) ≠ 0 := ne_of_gt hpos
  have hnum : HasDerivAt (fun t : ℝ => L * Real.exp (-(t * L)))
      (L * (-L * Real.exp (-(s * L)))) s := (hasDerivAt_expNode L s).const_mul L
  have hquot := (hnum.div (hasDerivAt_oneSubExpNode L s) hne).neg
  rw [show L ^ 2 * Real.exp (-(s * L)) / (1 - Real.exp (-(s * L))) ^ 2 =
      -((L * (-L * Real.exp (-(s * L))) * (1 - Real.exp (-(s * L))) -
          L * Real.exp (-(s * L)) * (L * Real.exp (-(s * L)))) /
        (1 - Real.exp (-(s * L))) ^ 2) by field_simp; ring]
  exact hquot

private theorem hasDerivAt_localLogD2 {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => L ^ 2 * Real.exp (-(t * L)) / (1 - Real.exp (-(t * L))) ^ 2)
      (-(L ^ 3 * (Real.exp (-(s * L)) * (1 + Real.exp (-(s * L)))) /
        (1 - Real.exp (-(s * L))) ^ 3)) s := by
  have hpos := one_sub_exp_node_pos hL hs
  have hne : (1 - Real.exp (-(s * L))) ≠ 0 := ne_of_gt hpos
  have hden : HasDerivAt (fun t : ℝ => (1 - Real.exp (-(t * L))) ^ 2)
      ((2 : ℝ) * (1 - Real.exp (-(s * L))) ^ 1 * (L * Real.exp (-(s * L)))) s :=
    (hasDerivAt_oneSubExpNode L s).pow 2
  have hdenne : ((1 - Real.exp (-(s * L))) ^ 2) ≠ 0 := pow_ne_zero _ hne
  have hnum : HasDerivAt (fun t : ℝ => L ^ 2 * Real.exp (-(t * L)))
      (L ^ 2 * (-L * Real.exp (-(s * L)))) s := (hasDerivAt_expNode L s).const_mul (L ^ 2)
  have hquot := hnum.div hden hdenne
  rw [show -(L ^ 3 * (Real.exp (-(s * L)) * (1 + Real.exp (-(s * L)))) /
        (1 - Real.exp (-(s * L))) ^ 3) =
      (L ^ 2 * (-L * Real.exp (-(s * L))) * (1 - Real.exp (-(s * L))) ^ 2 -
          L ^ 2 * Real.exp (-(s * L)) *
            ((2 : ℝ) * (1 - Real.exp (-(s * L))) ^ 1 * (L * Real.exp (-(s * L))))) /
        ((1 - Real.exp (-(s * L))) ^ 2) ^ 2 by field_simp; ring]
  exact hquot

private theorem iteratedDeriv_three_localLog {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    iteratedDeriv 3 (fun t : ℝ => -Real.log (1 - Real.exp (-(t * L)))) s =
      -(L ^ 3 * (Real.exp (-(s * L)) * (1 + Real.exp (-(s * L)))) /
        (1 - Real.exp (-(s * L))) ^ 3) := by
  set f : ℝ → ℝ := fun t : ℝ => -Real.log (1 - Real.exp (-(t * L))) with hf
  set g : ℝ → ℝ := fun t : ℝ => -(L * Real.exp (-(t * L)) / (1 - Real.exp (-(t * L)))) with hg
  set h : ℝ → ℝ := fun t : ℝ =>
    L ^ 2 * Real.exp (-(t * L)) / (1 - Real.exp (-(t * L))) ^ 2 with hh
  have hthree : iteratedDeriv 3 f = deriv (deriv (deriv f)) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
      show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv1 : EqOn (deriv f) g (Ioi 0) := fun t ht => (hasDerivAt_localLog hL ht).deriv
  have hderiv2 : EqOn (deriv g) h (Ioi 0) := fun t ht => (hasDerivAt_localLogD1 hL ht).deriv
  have hd2 : deriv (deriv f) =ᶠ[nhds s] h := by
    refine Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hs) fun t ht => ?_
    have hlocal : deriv f =ᶠ[nhds t] g :=
      Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds ht) hderiv1
    rw [hlocal.deriv_eq]
    exact hderiv2 ht
  rw [hthree, hd2.deriv_eq]
  exact (hasDerivAt_localLogD2 hL hs).deriv

/-! ## The explicit prime-power form of the cubic jet -/

/-- The local Euler-log third jet at the critical abscissa, in closed form. -/
private theorem iteratedDeriv_three_local {p : ℕ} (hp : p.Prime) :
    iteratedDeriv 3 (fun t : ℝ => -Real.log (1 - (p : ℝ) ^ (-t))) 1 =
      -(Real.log (p : ℝ) ^ 3 * ((p : ℝ)⁻¹ * (1 + (p : ℝ)⁻¹)) / (1 - (p : ℝ)⁻¹) ^ 3) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hL : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hfun : (fun t : ℝ => -Real.log (1 - (p : ℝ) ^ (-t)))
      = fun t : ℝ => -Real.log (1 - Real.exp (-(t * Real.log (p : ℝ)))) := by
    funext t
    rw [Real.rpow_def_of_pos hp0,
      show Real.log (p : ℝ) * (-t) = -(t * Real.log (p : ℝ)) by ring]
  rw [hfun, iteratedDeriv_three_localLog hL one_pos]
  have hnode : Real.exp (-((1 : ℝ) * Real.log (p : ℝ))) = (p : ℝ)⁻¹ := by
    rw [one_mul, Real.exp_neg, Real.exp_log hp0]
  rw [hnode]

/-- **The cubic confluence jet of the finite Euler logarithm.**  The third derivative of `P_N` at
the critical abscissa is the negative of an explicit positive prime current. -/
theorem iteratedDeriv_three_primeEulerLogBelow (N : ℕ) :
    iteratedDeriv 3 (fun s => primeEulerLogBelow s N) 1 =
      ∑ p ∈ Nat.primesBelow N,
        -(Real.log (p : ℝ) ^ 3 * ((p : ℝ)⁻¹ * (1 + (p : ℝ)⁻¹)) / (1 - (p : ℝ)⁻¹) ^ 3) := by
  have heq : (fun s => primeEulerLogBelow s N)
      =ᶠ[nhds (1 : ℝ)] fun t : ℝ => ∑ p ∈ Nat.primesBelow N, -Real.log (1 - (p : ℝ) ^ (-t)) := by
    refine Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds (by norm_num : (1 : ℝ) ∈ Ioi 0)) ?_
    intro t ht
    exact primeEulerLogBelow_eq_sum ht N
  rw [Filter.EventuallyEq.iteratedDeriv_eq 3 heq]
  rw [iteratedDeriv_fun_sum (fun p hp =>
    contDiffAt_neg_log_one_sub_rpow (Nat.prime_of_mem_primesBelow hp) 3 one_pos)]
  exact Finset.sum_congr rfl fun p hp =>
    iteratedDeriv_three_local (Nat.prime_of_mem_primesBelow hp)

/-! ## The positive prime-power annulus current -/

/-- The local cubic confluence current of one ordinary prime. -/
def cubicAnnulusPrimeCurrent (p : ℕ) : ℝ :=
  12 * Real.log (p : ℝ) ^ 3 * ∑' k : ℕ, (k : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ k

private theorem abs_inv_lt_one {p : ℕ} (hp : p.Prime) : |((p : ℝ)⁻¹)| < 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  rw [abs_of_pos (by positivity : (0 : ℝ) < (p : ℝ)⁻¹)]
  rw [inv_lt_one_iff₀]
  exact Or.inr hp1

/-- The prime-power second moment of the geometric depth law in closed form. -/
theorem tsum_sq_mul_prime_pow {p : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, (k : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ k) =
      (p : ℝ)⁻¹ * (1 + (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 3 :=
  (hasSum_sq_mul_geometric_of_abs_lt_one (abs_inv_lt_one hp)).tsum_eq

/-- Closed form of the local cubic current. -/
theorem cubicAnnulusPrimeCurrent_eq {p : ℕ} (hp : p.Prime) :
    cubicAnnulusPrimeCurrent p =
      12 * Real.log (p : ℝ) ^ 3 *
        ((p : ℝ)⁻¹ * (1 + (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 3) := by
  rw [cubicAnnulusPrimeCurrent, tsum_sq_mul_prime_pow hp]

/-- The local cubic current is strictly positive. -/
theorem cubicAnnulusPrimeCurrent_pos {p : ℕ} (hp : p.Prime) :
    0 < cubicAnnulusPrimeCurrent p := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hL : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hq : 0 < (p : ℝ)⁻¹ := by positivity
  have hq1 : (p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    exact Or.inr hp1
  rw [cubicAnnulusPrimeCurrent_eq hp]
  have hden : 0 < (1 - (p : ℝ)⁻¹) ^ 3 := by positivity
  positivity

/-- **The exact cubic confluence order.**  The third jet of the reflected Hellinger sewing cost is
the positive prime-power annulus current. -/
theorem iteratedDeriv_three_logReflectedSewing_eq_cubicAnnulusCurrent (N : ℕ) :
    iteratedDeriv 3 (fun c => logReflectedSewingBelow c N) 0 =
      ∑ p ∈ Nat.primesBelow N, cubicAnnulusPrimeCurrent p := by
  rw [iteratedDeriv_three_logReflectedSewing N, iteratedDeriv_three_primeEulerLogBelow N,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [cubicAnnulusPrimeCurrent_eq (Nat.prime_of_mem_primesBelow hp)]
  ring

/-- The cubic jet in the card's prime-power series form. -/
theorem iteratedDeriv_three_logReflectedSewing_eq_tsum (N : ℕ) :
    iteratedDeriv 3 (fun c => logReflectedSewingBelow c N) 0 =
      12 * ∑ p ∈ Nat.primesBelow N,
        ∑' k : ℕ, (k : ℝ) ^ 2 * Real.log (p : ℝ) ^ 3 * ((p : ℝ)⁻¹) ^ k := by
  rw [iteratedDeriv_three_logReflectedSewing_eq_cubicAnnulusCurrent N, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [cubicAnnulusPrimeCurrent, mul_assoc, ← tsum_mul_left]
  congr 1
  exact tsum_congr fun k => by ring

/-- **Strict positivity of the cubic confluence order.** -/
theorem iteratedDeriv_three_logReflectedSewing_pos {N : ℕ} (hN : 2 < N) :
    0 < iteratedDeriv 3 (fun c => logReflectedSewingBelow c N) 0 := by
  rw [iteratedDeriv_three_logReflectedSewing_eq_cubicAnnulusCurrent N]
  refine Finset.sum_pos (fun p hp => cubicAnnulusPrimeCurrent_pos
    (Nat.prime_of_mem_primesBelow hp)) ⟨2, Nat.mem_primesBelow.mpr ⟨hN, Nat.prime_two⟩⟩

/-! ## Wold activation and the synchronized Gamma second moment -/

/-- At unit aperture the synchronized disk node is the ordinary prime reciprocal. -/
theorem xiMobiusContinuousApertureDiskNode_one (p : Nat.Primes) :
    xiMobiusContinuousApertureDiskNode 1 p = ((p : ℕ) : ℝ)⁻¹ := by
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  rw [xiMobiusContinuousApertureDiskNode, neg_mul, one_mul, Real.exp_neg, Real.exp_log hp0]

/-- The all-positive-depth geometric Wold activation of one prime ray. -/
def woldGeometricActivation (p : ℕ) : ℝ := (p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹)

/-- The complete synchronized Gamma half-height second moment of one prime ray. -/
def gammaSewnSynchronizedEulerHalfHeightSecondMoment (p : Nat.Primes) : ℝ :=
  ∑' e : ℕ,
    gammaSewnSynchronizedEulerDepthProbability 1 p e * xiGammaEulerBoundaryHalfHeight p e ^ 2

/-- **The synchronized Euler depth theorem at unit aperture.**  The complete second moment of the
physical half-height over one prime ray is `L^2 (1 + q) / (4 (1 - q)^2)` at `q = p⁻¹`. -/
theorem gammaSewnSynchronizedEulerHalfHeightSecondMoment_eq (p : Nat.Primes) :
    gammaSewnSynchronizedEulerHalfHeightSecondMoment p =
      Real.log ((p : ℕ) : ℝ) ^ 2 * (1 + ((p : ℕ) : ℝ)⁻¹) /
        (4 * (1 - ((p : ℕ) : ℝ)⁻¹) ^ 2) := by
  have h := (hasSum_gammaSewnSynchronizedEulerDepthProbability_mul_halfHeight_sq
    (x := 1) one_pos p).tsum_eq
  rw [gammaSewnSynchronizedEulerHalfHeightSecondMoment, h,
    xiMobiusContinuousApertureDiskNode_one]

/-- **Exact local Wold/Gamma factorization of the cubic annulus current.**  The dyadic-confluence
normalization `48 log p` is forced; the two remaining factors are the geometric Wold activation and
the complete synchronized Gamma second moment of the same prime ray. -/
theorem cubicAnnulusPrimeCurrent_eq_woldActivation_mul_secondMoment (p : Nat.Primes) :
    cubicAnnulusPrimeCurrent (p : ℕ) =
      48 * Real.log ((p : ℕ) : ℝ) * woldGeometricActivation (p : ℕ) *
        gammaSewnSynchronizedEulerHalfHeightSecondMoment p := by
  have hp := p.2
  have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp.one_lt
  have hq1 : ((p : ℕ) : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    exact Or.inr hp1
  have hne : (1 - ((p : ℕ) : ℝ)⁻¹) ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact absurd h.symm (ne_of_lt hq1)
  rw [cubicAnnulusPrimeCurrent_eq hp, gammaSewnSynchronizedEulerHalfHeightSecondMoment_eq,
    woldGeometricActivation]
  field_simp
  ring

end

end RHTower
