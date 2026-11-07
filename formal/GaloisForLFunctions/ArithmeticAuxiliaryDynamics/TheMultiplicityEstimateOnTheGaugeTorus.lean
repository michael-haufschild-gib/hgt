import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheCoefficientMassOfAProducer
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheMellinTransformOfAStencil
import GaloisForLFunctions.HTGeometry.UniformZeroCountBound
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The multiplicity estimate on the gauge torus

A point `ω` of the gauge torus twists a stencil to `D_c^ω(s) = Σ c(k) ω(k) k^{-s}`. The twist is an
exponential polynomial in `s`, with exponents `log k`.

* **Multiplicity.** The derivatives at `s` are the moments `Σ c(k) ω(k) k^{-s} (log k)^r`, a Vandermonde
  system in the distinct nodes `log k`. So at every point of the plane and every point of the torus the
  order of vanishing is below the number of letters. This is the only local constraint: nothing in it
  depends on the size of the coefficients, and it does not see arithmetic.
* **Zeros.** Jensen's formula with the value at a point far to the right bounds the zeros in a disc of
  radius `r` by `(log(2 Σ|c(k)| / |c(1)|) + 2 r log K) / log 2`, uniformly on the torus.
* **Adams operators.** `ψ_j` sends the letter `k` to `k^j`, and `D^ω_{ψ_j c}(s) = D^{ω^j}_c(j s)`. It keeps
  the number of letters and raises the alphabet to the power `j`, so it cannot raise a multiplicity
  estimate.

A zero of a producer's polynomial near a zero of `ζ` is therefore cheap: no zero estimate of this type
limits the auxiliary. What limits it is the rate law, which reads the whole multiplicity function.
-/

open Finset Metric
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The `r`-th logarithmic moment of a stencil twisted by `ω`. -/
def logMoment (c : ℕ →₀ ℤ) (ω : ℕ → ℂ) (r : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ c.support, (c k : ℂ) * ω k * ((Real.log k : ℝ) : ℂ) ^ r * ((k : ℝ) : ℂ) ^ (-s)

/-- The stencil twisted by a point of the gauge torus. -/
def gaugeTwist (c : ℕ →₀ ℤ) (ω : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ k ∈ c.support, (c k : ℂ) * ω k * ((k : ℝ) : ℂ) ^ (-s)

theorem gaugeTwist_eq_logMoment (c : ℕ →₀ ℤ) (ω : ℕ → ℂ) : gaugeTwist c ω = logMoment c ω 0 := by
  funext s
  simp [gaugeTwist, logMoment]

/-- The trivial gauge point gives the Dirichlet polynomial. -/
theorem gaugeTwist_one (c : ℕ →₀ ℤ) : gaugeTwist c (fun _ => 1) = dirichletPoly c := by
  funext s
  simp [gaugeTwist, dirichletPoly]

private lemma ofReal_natCast_ne_zero {k : ℕ} (hk : k ≠ 0) : (((k : ℝ) : ℂ)) ≠ 0 := by
  simpa using hk

/-- Differentiating lowers the exponent of the phase and raises the moment. -/
theorem hasDerivAt_logMoment {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (ω : ℕ → ℂ) (r : ℕ) (s : ℂ) :
    HasDerivAt (logMoment c ω r) (-logMoment c ω (r + 1) s) s := by
  have hterm : ∀ k ∈ c.support, HasDerivAt
      (fun s : ℂ => (c k : ℂ) * ω k * ((Real.log k : ℝ) : ℂ) ^ r * ((k : ℝ) : ℂ) ^ (-s))
      (-((c k : ℂ) * ω k * ((Real.log k : ℝ) : ℂ) ^ (r + 1) * ((k : ℝ) : ℂ) ^ (-s))) s := by
    intro k hk
    have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
    have hbase := ofReal_natCast_ne_zero hk0
    have hd := ((hasDerivAt_neg s).const_cpow (c := ((k : ℝ) : ℂ)) (Or.inl hbase)).const_mul
      ((c k : ℂ) * ω k * ((Real.log k : ℝ) : ℂ) ^ r)
    refine hd.congr_deriv ?_
    rw [← Complex.ofReal_log (Nat.cast_nonneg k)]
    ring
  have hsum := HasDerivAt.fun_sum hterm
  have hfun : (logMoment c ω r) = fun s : ℂ => ∑ k ∈ c.support,
      (c k : ℂ) * ω k * ((Real.log k : ℝ) : ℂ) ^ r * ((k : ℝ) : ℂ) ^ (-s) := rfl
  rw [hfun, logMoment, ← sum_neg_distrib]
  exact hsum

theorem differentiable_logMoment {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (ω : ℕ → ℂ) (r : ℕ) :
    Differentiable ℂ (logMoment c ω r) :=
  fun s => (hasDerivAt_logMoment hc0 ω r s).differentiableAt

/-- The derivatives of the twist are the moments, up to sign. -/
theorem iteratedDeriv_gaugeTwist {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (ω : ℕ → ℂ) (r : ℕ) :
    iteratedDeriv r (gaugeTwist c ω) = fun s => (-1) ^ r * logMoment c ω r s := by
  induction r with
  | zero =>
    rw [iteratedDeriv_zero, gaugeTwist_eq_logMoment]
    funext s
    simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    have hd := ((hasDerivAt_logMoment hc0 ω r s).const_mul ((-1 : ℂ) ^ r)).deriv
    rw [hd, pow_succ]
    ring

/-- **The Vandermonde step.** The first `|supp c|` moments of a nonzero stencil do not all vanish, at any
point of the plane and any gauge point nonvanishing on its letters. -/
theorem exists_logMoment_ne_zero {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hc : c ≠ 0) {ω : ℕ → ℂ}
    (hω : ∀ k ∈ c.support, ω k ≠ 0) (s : ℂ) :
    ∃ r < c.support.card, logMoment c ω r s ≠ 0 := by
  classical
  by_contra hall
  push Not at hall
  set e := c.support.equivFin with he
  set a : c.support → ℂ := fun k => (c k : ℂ) * ω k * (((k : ℕ) : ℝ) : ℂ) ^ (-s) with ha
  set f : Fin c.support.card → ℂ := fun j => ((Real.log ((e.symm j : ℕ) : ℝ) : ℝ) : ℂ) with hf
  have hk_pos : ∀ k : c.support, (0 : ℝ) < ((k : ℕ) : ℝ) := by
    intro k
    have hk0 : (k : ℕ) ≠ 0 := fun h => by
      have := Finsupp.mem_support_iff.mp k.2
      rw [h] at this
      exact this hc0
    exact_mod_cast Nat.pos_of_ne_zero hk0
  have hinj : Function.Injective f := by
    intro i j hij
    have hreal : Real.log ((e.symm i : ℕ) : ℝ) = Real.log ((e.symm j : ℕ) : ℝ) :=
      Complex.ofReal_injective hij
    have hcast := Real.log_injOn_pos (Set.mem_Ioi.mpr (hk_pos _)) (Set.mem_Ioi.mpr (hk_pos _)) hreal
    have hnat : (e.symm i : ℕ) = (e.symm j : ℕ) := by exact_mod_cast hcast
    exact e.symm.injective (Subtype.ext hnat)
  have hzero : (fun j => a (e.symm j)) = 0 := by
    refine Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hinj fun i => ?_
    have hm := hall i i.2
    have hsum : ∑ j : Fin c.support.card, a (e.symm j) * f j ^ (i : ℕ) =
        ∑ k : c.support, a k * ((Real.log ((k : ℕ) : ℝ) : ℝ) : ℂ) ^ (i : ℕ) :=
      Equiv.sum_comp e.symm (fun k : c.support => a k * ((Real.log ((k : ℕ) : ℝ) : ℝ) : ℂ) ^ (i : ℕ))
    rw [hsum]
    rw [logMoment, ← Finset.sum_coe_sort] at hm
    rw [← hm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [ha]
    ring
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, k₀ ∈ c.support := Finsupp.support_nonempty_iff.mpr hc
  have hval : a ⟨k₀, hk₀⟩ = 0 := by
    have := congrFun hzero (e ⟨k₀, hk₀⟩)
    simpa using this
  simp only [ha] at hval
  have hk0 : k₀ ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk₀ hc0
  have hc1 : (c k₀ : ℂ) ≠ 0 := by exact_mod_cast Finsupp.mem_support_iff.mp hk₀
  have hpow : (((k₀ : ℝ) : ℂ)) ^ (-s) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (ofReal_natCast_ne_zero hk0)]
    exact Complex.exp_ne_zero _
  exact mul_ne_zero (mul_ne_zero hc1 (hω k₀ hk₀)) hpow hval

/-- **The multiplicity estimate.** The order of vanishing of a nonzero twisted stencil at any point is
below the number of its letters. -/
theorem analyticOrderAt_gaugeTwist_lt {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hc : c ≠ 0) {ω : ℕ → ℂ}
    (hω : ∀ k ∈ c.support, ω k ≠ 0) (s : ℂ) :
    analyticOrderAt (gaugeTwist c ω) s < (c.support.card : ℕ∞) := by
  have hdiff : Differentiable ℂ (gaugeTwist c ω) := by
    rw [gaugeTwist_eq_logMoment]
    exact differentiable_logMoment hc0 ω 0
  by_contra h
  push Not at h
  have hall := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hdiff.analyticAt s)).mp h
  obtain ⟨r, hr, hne⟩ := exists_logMoment_ne_zero hc0 hc hω s
  have hz := hall r hr
  rw [iteratedDeriv_gaugeTwist hc0] at hz
  have hz' : (-1 : ℂ) ^ r * logMoment c ω r s = 0 := hz
  rcases mul_eq_zero.mp hz' with h0 | h0
  · exact absurd h0 (pow_ne_zero _ (by norm_num))
  · exact hne h0

private lemma one_le_of_mem_support {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) {k : ℕ} (hk : k ∈ c.support) :
    (1 : ℝ) ≤ k := by
  have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
  exact_mod_cast Nat.pos_of_ne_zero hk0

/-- The size of a unitary twist to the right of `Re s = −R`. -/
theorem norm_gaugeTwist_le {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) {ω : ℕ → ℂ}
    (hω : ∀ k ∈ c.support, ‖ω k‖ = 1) {K : ℕ} (hal : AlphabetLE c K) {R : ℝ} (hR : 0 ≤ R) {s : ℂ}
    (hs : -R ≤ s.re) : ‖gaugeTwist c ω s‖ ≤ coeffMass c * (K : ℝ) ^ R := by
  rw [gaugeTwist, coeffMass, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun k hk => ?_)
  have hk1 := one_le_of_mem_support hc0 hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hkK : (k : ℝ) ≤ K := by exact_mod_cast hal k hk
  rw [norm_mul, norm_mul, hω k hk, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos hkpos, Complex.neg_re,
    Complex.norm_intCast]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc (k : ℝ) ^ (-s.re) ≤ (k : ℝ) ^ R := Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
    _ ≤ (K : ℝ) ^ R := Real.rpow_le_rpow hkpos.le hkK hR

/-- A real point far to the right, where the letter `1` dominates. -/
theorem le_norm_gaugeTwist {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hc1 : c 1 ≠ 0) {ω : ℕ → ℂ}
    (hω : ∀ k ∈ c.support, ‖ω k‖ = 1) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : coeffMass c * (2 : ℝ) ^ (-σ) ≤ |(c 1 : ℝ)| / 2) :
    |(c 1 : ℝ)| / 2 ≤ ‖gaugeTwist c ω (σ : ℂ)‖ := by
  classical
  have h1 : 1 ∈ c.support := Finsupp.mem_support_iff.mpr hc1
  have hsplit : gaugeTwist c ω (σ : ℂ) = (c 1 : ℂ) * ω 1 * (((1 : ℕ) : ℝ) : ℂ) ^ (-(σ : ℂ)) +
      ∑ k ∈ c.support.erase 1, (c k : ℂ) * ω k * ((k : ℝ) : ℂ) ^ (-(σ : ℂ)) := by
    rw [gaugeTwist, ← add_sum_erase _ _ h1]
  rw [hsplit]
  have hhead : ‖(c 1 : ℂ) * ω 1 * (((1 : ℕ) : ℝ) : ℂ) ^ (-(σ : ℂ))‖ = |(c 1 : ℝ)| := by
    rw [norm_mul, norm_mul, hω 1 h1, mul_one]
    simp
  have htail : ‖∑ k ∈ c.support.erase 1, (c k : ℂ) * ω k * ((k : ℝ) : ℂ) ^ (-(σ : ℂ))‖ ≤
      coeffMass c * (2 : ℝ) ^ (-σ) := by
    refine (norm_sum_le _ _).trans ?_
    rw [coeffMass, sum_mul]
    refine (sum_le_sum fun k hk => ?_).trans (sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
      fun k _ _ => by positivity)
    have hk' := mem_erase.mp hk
    have hk1 := one_le_of_mem_support hc0 hk'.2
    have hk2 : (2 : ℝ) ≤ k := by
      have h0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk'.2 hc0
      have : 2 ≤ k := by omega
      exact_mod_cast this
    have hkpos : (0 : ℝ) < k := by linarith
    rw [norm_mul, norm_mul, hω k hk'.2, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos hkpos,
      Complex.neg_re, Complex.ofReal_re, Complex.norm_intCast]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) hk2 (by linarith)
  have hrev : ‖(c 1 : ℂ) * ω 1 * (((1 : ℕ) : ℝ) : ℂ) ^ (-(σ : ℂ))‖ -
      ‖∑ k ∈ c.support.erase 1, (c k : ℂ) * ω k * ((k : ℝ) : ℂ) ^ (-(σ : ℂ))‖ ≤
      ‖(c 1 : ℂ) * ω 1 * (((1 : ℕ) : ℝ) : ℂ) ^ (-(σ : ℂ)) +
        ∑ k ∈ c.support.erase 1, (c k : ℂ) * ω k * ((k : ℝ) : ℂ) ^ (-(σ : ℂ))‖ := by
    have h := norm_sub_norm_le ((c 1 : ℂ) * ω 1 * (((1 : ℕ) : ℝ) : ℂ) ^ (-(σ : ℂ)))
      (-∑ k ∈ c.support.erase 1, (c k : ℂ) * ω k * ((k : ℝ) : ℂ) ^ (-(σ : ℂ)))
    rwa [norm_neg, sub_neg_eq_add] at h
  rw [hhead] at hrev
  have h2 := le_trans (sub_le_sub_left (htail.trans hσ) _) hrev
  calc |(c 1 : ℝ)| / 2 = |(c 1 : ℝ)| - |(c 1 : ℝ)| / 2 := by ring
    _ ≤ _ := h2

/-- **The zero estimate on the torus.** A unitary twist of a stencil on the alphabet `[1, K]` has at most
`(log (2 Σ|c(k)| / |c(1)|) + 2 r log K) / log 2` zeros in a disc of radius `r` about a point far to the
right, uniformly in the gauge point. -/
theorem sum_divisor_gaugeTwist_le {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hc1 : c 1 ≠ 0) {K : ℕ} (hK : 1 ≤ K)
    (hal : AlphabetLE c K) {ω : ℕ → ℂ} (hω : ∀ k ∈ c.support, ‖ω k‖ = 1) {σ r : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : coeffMass c * (2 : ℝ) ^ (-σ) ≤ |(c 1 : ℝ)| / 2) (hr : 0 < r) :
    ∑ᶠ u, MeromorphicOn.divisor (gaugeTwist c ω) (closedBall (σ : ℂ) |r|) u ≤
      (Real.log (2 * coeffMass c / |(c 1 : ℝ)|) + 2 * r * Real.log K) / Real.log 2 := by
  classical
  have hc1R : (1 : ℝ) ≤ |(c 1 : ℝ)| := by
    have : (1 : ℤ) ≤ |c 1| := Int.one_le_abs hc1
    exact_mod_cast this
  have h1 : 1 ∈ c.support := Finsupp.mem_support_iff.mpr hc1
  have hmass : |(c 1 : ℝ)| ≤ coeffMass c := by
    rw [coeffMass]
    exact single_le_sum (f := fun k => |(c k : ℝ)|) (fun _ _ => abs_nonneg _) h1
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hr2 : 0 ≤ 2 * r := by linarith
  have hKpow : (1 : ℝ) ≤ (K : ℝ) ^ (2 * r) := Real.one_le_rpow hKR hr2
  have hdiff : Differentiable ℂ (gaugeTwist c ω) := by
    rw [gaugeTwist_eq_logMoment]
    exact differentiable_logMoment hc0 ω 0
  have hmass1 : (1 : ℝ) ≤ coeffMass c := hc1R.trans hmass
  have hbound := HTGeometry.sum_divisor_le_of_bounds (c := (σ : ℂ)) (r := r) (R := 2 * r)
    (M := coeffMass c * (K : ℝ) ^ (2 * r)) (m := |(c 1 : ℝ)| / 2) (f := gaugeTwist c ω)
    (by rw [abs_of_pos hr]; exact hr)
    (by rw [abs_of_pos hr, abs_of_pos (by linarith)]; linarith)
    (by nlinarith) (by linarith)
    (fun z _ => hdiff.analyticAt z)
    (le_norm_gaugeTwist hc0 hc1 hω hσ0 hσ)
    (fun z hz => norm_gaugeTwist_le hc0 hω hal hr2 (by
      have hd : dist z (σ : ℂ) = |2 * r| := mem_sphere.mp hz
      rw [abs_of_pos (by linarith)] at hd
      have hre : |z.re - σ| ≤ 2 * r := by
        have := Complex.abs_re_le_norm (z - (σ : ℂ))
        rw [Complex.sub_re, Complex.ofReal_re] at this
        rw [dist_eq_norm] at hd
        rwa [hd] at this
      have := (abs_le.mp hre).1
      linarith))
  refine hbound.trans (le_of_eq ?_)
  have hratio : 2 * r / r = 2 := by field_simp
  rw [hratio]
  congr 1
  have hc1pos : 0 < |(c 1 : ℝ)| := by linarith
  have hmasspos : 0 < coeffMass c := by linarith
  have hKpos : (0 : ℝ) < (K : ℝ) ^ (2 * r) := by positivity
  have hsplit : coeffMass c * (K : ℝ) ^ (2 * r) / (|(c 1 : ℝ)| / 2) =
      (2 * coeffMass c / |(c 1 : ℝ)|) * (K : ℝ) ^ (2 * r) := by
    field_simp
  rw [hsplit, Real.log_mul (by positivity) hKpos.ne', Real.log_rpow (by linarith)]

/-- The Adams operator: the letter `k` becomes `k^j`. -/
def adams (j : ℕ) (c : ℕ →₀ ℤ) : ℕ →₀ ℤ := c.mapDomain (· ^ j)

/-- **Adams keeps the number of letters**, so it cannot raise the multiplicity estimate. -/
theorem card_support_adams {j : ℕ} (hj : 0 < j) (c : ℕ →₀ ℤ) :
    (adams j c).support.card = c.support.card := by
  classical
  have hinj : Function.Injective (· ^ j : ℕ → ℕ) := Nat.pow_left_injective hj.ne'
  rw [adams, Finsupp.mapDomain_support_of_injective hinj, card_image_of_injective _ hinj]

/-- **The Adams duality.** For multiplicative `ω`, `D^ω_{ψ_j c}(s) = D^{ω^j}_c(j s)`. -/
theorem gaugeTwist_adams {j : ℕ} {c : ℕ →₀ ℤ} {ω : ℕ → ℂ} (h1 : ω 1 = 1)
    (hmul : ∀ a b, ω (a * b) = ω a * ω b) (s : ℂ) :
    gaugeTwist (adams j c) ω s = gaugeTwist c (fun k => ω k ^ j) ((j : ℂ) * s) := by
  have hpow : ∀ k n, ω (k ^ n) = ω k ^ n := by
    intro k n
    induction n with
    | zero => simp [h1]
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
  have hsum : ∀ d : ℕ →₀ ℤ, gaugeTwist d ω s =
      d.sum fun k a => (a : ℂ) * ω k * ((k : ℝ) : ℂ) ^ (-s) := fun _ => rfl
  have hsum' : ∀ d : ℕ →₀ ℤ, gaugeTwist d (fun k => ω k ^ j) ((j : ℂ) * s) =
      d.sum fun k a => (a : ℂ) * ω k ^ j * ((k : ℝ) : ℂ) ^ (-((j : ℂ) * s)) := fun _ => rfl
  rw [hsum, hsum', adams, Finsupp.sum_mapDomain_index (by simp) (by intro _ a b; push_cast; ring)]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [hpow]
  have hcp : (((k ^ j : ℕ) : ℝ) : ℂ) ^ (-s) = ((k : ℝ) : ℂ) ^ (-((j : ℂ) * s)) := by
    have h := Complex.natCast_cpow_natCast_mul k j (-s)
    rw [mul_neg] at h
    simp only [Nat.cast_pow, Complex.ofReal_pow, Complex.ofReal_natCast]
    exact h.symm
  rw [hcp]

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
