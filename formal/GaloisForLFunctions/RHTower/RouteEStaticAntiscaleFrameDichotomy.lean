import GaloisForLFunctions.RHTower.GibbsAntiscaleFirstTraceFrame
import GaloisForLFunctions.HTGeometry.KroneckerApproxRecurrence

/-!
# Static all-prime antiscale-frame dichotomy

A fixed nonnegative diagonal weighting of the complete prime antiscale frame has only two
possibilities.  If its reciprocal-prime mass is summable, simultaneous recurrence of every finite
prime head to phase `-1`, followed by summable-tail control, makes the complete frame energy
arbitrarily small at arbitrarily large frequencies.  If that mass is not summable, the frame is
already undefined as a summable nonnegative quadratic form at frequency zero.

Thus no fixed nonnegative diagonal all-prime weight is both finite at every frequency and
uniformly coercive.  The theorem does not cover moving-aperture weights or off-diagonal kernels.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

open GaloisForLFunctions

/-- Reciprocal-prime mass of a static prime weight. -/
def routeEStaticAntiscaleMass (omega : Nat.Primes → ℝ) (p : Nat.Primes) : ℝ :=
  omega p / ((p : ℕ) : ℝ)

/-- One term of the static all-prime antiscale frame. -/
def routeEStaticAntiscaleTerm
    (omega : Nat.Primes → ℝ) (p : Nat.Primes) (t : ℝ) : ℝ :=
  routeEStaticAntiscaleMass omega p *
    Complex.normSq (1 + charFn t ((p : Nat.Primes) : ℕ))

theorem routeEStaticAntiscaleMass_nonneg
    {omega : Nat.Primes → ℝ} (homega : ∀ p, 0 ≤ omega p) (p : Nat.Primes) :
    0 ≤ routeEStaticAntiscaleMass omega p := by
  exact div_nonneg (homega p) (by positivity)

theorem routeEStaticAntiscaleTerm_nonneg
    {omega : Nat.Primes → ℝ} (homega : ∀ p, 0 ≤ omega p)
    (p : Nat.Primes) (t : ℝ) :
    0 ≤ routeEStaticAntiscaleTerm omega p t := by
  exact mul_nonneg (routeEStaticAntiscaleMass_nonneg homega p) (Complex.normSq_nonneg _)

/-- Every static antiscale term is bounded by four times its reciprocal-prime mass. -/
theorem routeEStaticAntiscaleTerm_le_four_mass
    {omega : Nat.Primes → ℝ} (homega : ∀ p, 0 ≤ omega p)
    (p : Nat.Primes) (t : ℝ) :
    routeEStaticAntiscaleTerm omega p t ≤ 4 * routeEStaticAntiscaleMass omega p := by
  have hcos : Real.cos (t * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) ≤ 1 :=
    Real.cos_le_one _
  rw [routeEStaticAntiscaleTerm, normSq_one_add_charFn]
  have hmass := routeEStaticAntiscaleMass_nonneg homega p
  nlinarith

/-- Finite reciprocal-prime mass makes the complete static frame summable at every frequency. -/
theorem summable_routeEStaticAntiscaleTerm
    {omega : Nat.Primes → ℝ} (homega : ∀ p, 0 ≤ omega p)
    (hsum : Summable (routeEStaticAntiscaleMass omega)) (t : ℝ) :
    Summable (fun p : Nat.Primes => routeEStaticAntiscaleTerm omega p t) := by
  refine Summable.of_nonneg_of_le
    (fun p => routeEStaticAntiscaleTerm_nonneg homega p t)
    (fun p => routeEStaticAntiscaleTerm_le_four_mass homega p t)
    (hsum.mul_left 4)

/-- At zero frequency the antiscale seam attains its pointwise ceiling exactly. -/
@[simp] theorem routeEStaticAntiscaleTerm_zero
    (omega : Nat.Primes → ℝ) (p : Nat.Primes) :
    routeEStaticAntiscaleTerm omega p 0 = 4 * routeEStaticAntiscaleMass omega p := by
  rw [routeEStaticAntiscaleTerm, normSq_one_add_charFn]
  simp
  ring

/-- Zero-frequency summability is exactly summability of the reciprocal-prime mass. -/
theorem summable_routeEStaticAntiscaleTerm_zero_iff
    (omega : Nat.Primes → ℝ) :
    Summable (fun p : Nat.Primes => routeEStaticAntiscaleTerm omega p 0) ↔
      Summable (routeEStaticAntiscaleMass omega) := by
  constructor
  · intro h
    have hscaled := h.mul_left (1 / 4 : ℝ)
    simpa using hscaled
  · intro h
    simpa using h.mul_left 4

/-- **Cofinal all-prime antiscale recurrence.**  Every summably weighted complete prime frame has
arbitrarily small energy at arbitrarily large frequencies. -/
theorem exists_gt_tsum_routeEStaticAntiscaleTerm_lt
    {omega : Nat.Primes → ℝ} (homega : ∀ p, 0 ≤ omega p)
    (hsum : Summable (routeEStaticAntiscaleMass omega))
    {delta : ℝ} (hdelta : 0 < delta) (T : ℝ) :
    ∃ t : ℝ, T < t ∧
      (∑' p : Nat.Primes, routeEStaticAntiscaleTerm omega p t) < delta := by
  classical
  have hsum4 : Summable (fun p : Nat.Primes => 4 * routeEStaticAntiscaleMass omega p) :=
    hsum.mul_left 4
  have hhalf : (0 : ℝ) < delta / 2 := by linarith
  have htail : Filter.Tendsto (fun s : Finset Nat.Primes =>
      ∑' p : {q : Nat.Primes // q ∉ s},
        4 * routeEStaticAntiscaleMass omega (p : Nat.Primes))
      Filter.atTop (nhds 0) :=
    tendsto_tsum_compl_atTop_zero
      (fun p : Nat.Primes => 4 * routeEStaticAntiscaleMass omega p)
  obtain ⟨P, hPtail⟩ := (htail.eventually_lt_const hhalf).exists
  set W : ℝ := ∑ p ∈ P, routeEStaticAntiscaleMass omega p with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun p _ => routeEStaticAntiscaleMass_nonneg homega p
  have hdenom : (0 : ℝ) < W + 1 := by linarith
  set epsilon : ℝ := Real.sqrt ((delta / 2) / (W + 1)) with hepsilon
  have hquot : (0 : ℝ) < (delta / 2) / (W + 1) := div_pos hhalf hdenom
  have hepsilon_pos : 0 < epsilon := Real.sqrt_pos.mpr hquot
  have hepsilon_sq : epsilon ^ 2 = (delta / 2) / (W + 1) :=
    Real.sq_sqrt hquot.le
  have hind : LinearIndependent ℚ
      (fun p : {q : Nat.Primes // q ∈ P} => Real.log (((p : Nat.Primes) : ℕ) : ℝ)) :=
    linearIndependent_log_primes.comp
      (fun p : {q : Nat.Primes // q ∈ P} => (p : Nat.Primes)) Subtype.val_injective
  obtain ⟨t, ht, hclose⟩ :=
    kronecker_approx_atTop hind (fun _ => Real.pi) hepsilon_pos T
  refine ⟨t, ht, ?_⟩
  have hsummable := summable_routeEStaticAntiscaleTerm homega hsum t
  have hsplit := hsummable.sum_add_tsum_compl (s := P)
  have hheadbound :
      (∑ p ∈ P, routeEStaticAntiscaleTerm omega p t) < delta / 2 := by
    have hterm : ∀ p ∈ P,
        routeEStaticAntiscaleTerm omega p t ≤
          routeEStaticAntiscaleMass omega p * epsilon ^ 2 := by
      intro p hp
      have hpclose := hclose ⟨p, hp⟩
      rw [Complex.exp_pi_mul_I] at hpclose
      have hchar : charFn t ((p : Nat.Primes) : ℕ) =
          expChar (Real.log (((p : Nat.Primes) : ℕ) : ℝ)) t := by
        rw [charFn, expChar]
        congr 2
        push_cast
        ring
      have hnorm : ‖1 + charFn t ((p : Nat.Primes) : ℕ)‖ < epsilon := by
        rw [show (1 : ℂ) + charFn t ((p : Nat.Primes) : ℕ) =
            charFn t ((p : Nat.Primes) : ℕ) - (-1) by ring, hchar]
        exact hpclose
      have hnormsq : Complex.normSq (1 + charFn t ((p : Nat.Primes) : ℕ)) <
          epsilon ^ 2 := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [norm_nonneg (1 + charFn t ((p : Nat.Primes) : ℕ))]
      rw [routeEStaticAntiscaleTerm]
      exact mul_le_mul_of_nonneg_left hnormsq.le
        (routeEStaticAntiscaleMass_nonneg homega p)
    calc
      (∑ p ∈ P, routeEStaticAntiscaleTerm omega p t)
          ≤ ∑ p ∈ P, routeEStaticAntiscaleMass omega p * epsilon ^ 2 :=
            Finset.sum_le_sum hterm
      _ = (∑ p ∈ P, routeEStaticAntiscaleMass omega p) * epsilon ^ 2 := by
            rw [Finset.sum_mul]
      _ = W * epsilon ^ 2 := by rw [hW]
      _ < delta / 2 := by
        rw [hepsilon_sq]
        have hrewrite :
            W * ((delta / 2) / (W + 1)) =
              (W * (delta / 2)) / (W + 1) := by ring
        rw [hrewrite, div_lt_iff₀ hdenom]
        nlinarith
  have htailbound :
      (∑' p : {q : Nat.Primes // q ∉ P},
        routeEStaticAntiscaleTerm omega (p : Nat.Primes) t) < delta / 2 := by
    refine lt_of_le_of_lt ?_ hPtail
    refine Summable.tsum_le_tsum (fun p => ?_)
      (hsummable.subtype _) (hsum4.subtype _)
    exact routeEStaticAntiscaleTerm_le_four_mass homega (p : Nat.Primes) t
  rw [← hsplit]
  have htailbound' :
      (∑' p : ((↑P : Set Nat.Primes)ᶜ : Set Nat.Primes),
        routeEStaticAntiscaleTerm omega (p : Nat.Primes) t) < delta / 2 := htailbound
  linarith

/-- **Static diagonal producer no-go.**  No fixed nonnegative all-prime diagonal weight gives a
summable frame at every frequency together with a positive frequency-uniform lower frame bound. -/
theorem not_exists_finite_uniformly_coercive_routeEStaticAntiscaleFrame :
    ¬ ∃ omega : Nat.Primes → ℝ,
      (∀ p, 0 ≤ omega p) ∧
      (∀ t : ℝ, Summable (fun p : Nat.Primes => routeEStaticAntiscaleTerm omega p t)) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ,
        c ≤ ∑' p : Nat.Primes, routeEStaticAntiscaleTerm omega p t := by
  rintro ⟨omega, homega, hfinite, c, hc, hcoercive⟩
  have hmass : Summable (routeEStaticAntiscaleMass omega) :=
    (summable_routeEStaticAntiscaleTerm_zero_iff omega).mp (hfinite 0)
  obtain ⟨t, _ht, hsmall⟩ :=
    exists_gt_tsum_routeEStaticAntiscaleTerm_lt homega hmass hc 0
  exact (not_lt_of_ge (hcoercive t)) hsmall

end

end RHTower.Sieve
