import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HeckeIncidenceCartesianLaw
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheResonatorRemainderIsNegative
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheSuccessorCollar

/-!
# The collar between towers and positivity of the finite-Euler-product form on lattice tests

On a single prime tower the prime self-intersection is the Toeplitz form `towerForm p M` bounded by
the Euler envelope `E_p = 2 log p/(√p − 1)` (`ResonatorKroneckerLaw.abs_towerForm_le`), and on
consecutive integers the prime incidence vanishes so the cycle pairing is the archimedean collar
alone (`TheSuccessorCollar.successor_localPair_bounds`). Across prime towers, the Cartesian law of
`HeckeIncidenceCartesianLaw` shows that two Hecke cycles `Γ_a, Γ_b` meet through the primes only
when their exponent vectors differ in a single prime coordinate.

This file resolves Open Problem 4 by establishing the complete multi-tower calculus of the prime
incidence, the archimedean collar, the pole pairing, and the finite-Euler-product quadratic form on
arbitrary finite sets of `P`-smooth integers and rank-`P` boxes:

1. **The rank-`P` Cartesian / Kronecker decomposition (`primeCofactor`,
   `heckeIncidence_eq_sum_primes`, `heckeFormOn_eq_sum_primeSliceForm`,
   `abs_heckeFormOn_le_sum_eulerEnvelope`, `primeSliceForm_towerProductBox_self`).**
   For every prime `p` and positive integer `a`, the prime-to-`p` cofactor
   `primeCofactor p a = a / p^{v_p(a)}` characterizes off-`p` valuation agreement:
   `primeCofactor p a = primeCofactor p b ↔ ∀ r ≠ p, v_r(a) = v_r(b)`
   (`primeCofactor_eq_iff_factorization_eq_off`). Consequently, on any finite set `P` of primes and
   any `P`-smooth positive integers `a, b`, the Hecke incidence decomposes as the exact sum over
   `p ∈ P` of the single-coordinate tower weights along the `p`-fibres (`heckeIncidence_eq_sum_primes`),
   the quadratic form `heckeFormOn S c` splits into `∑_{p ∈ P} primeSliceForm p S c` with zero
   cross-prime prime coupling (`heckeFormOn_eq_sum_primeSliceForm`), each slice is bounded by
   `E_p ∑_{a ∈ S} c(a)²` (`abs_primeSliceForm_le`), and the total prime self-intersection obeys
   `|heckeFormOn S c| ≤ (∑_{p ∈ P} E_p) ∑_{a ∈ S} c(a)²` (`abs_heckeFormOn_le_sum_eulerEnvelope`).
   On inductive rank-`P` product boxes `towerProductBox B p M`, the slices reduce to single-prime
   tower forms and the resonant train `c ≡ 1` attains `∑_{p ∈ P} E_p` asymptotically
   (`exists_towerForm_one_gt_of_lt_eulerEnvelope`, `exists_heckeForm_box_one_gt_of_lt_add_eulerEnvelope`).

2. **The rank-`P` resonator remainder (`crossLagOn`, `rankPResonatorRemainder`,
   `rankPResonatorRemainder_le`, `two_mul_resonatorWeight_sq_lt_eulerEnvelope`,
   `rankPResonatorRemainder_neg_of_card_le_three`).**
   For any ordered pair of distinct primes `(p, q)` and any finite set `S ⊂ ℕ_{>0}`, the anti-diagonal
   cross-lag form `crossLagOn p q S c = ∑_{a, b ∈ S, aq = bp} c(a) c(b)` satisfies
   `|crossLagOn p q S c| ≤ ∑_{a ∈ S} c(a)²` (`abs_crossLagOn_le`). Hence the rank-`P` resonator
   remainder `rankPResonatorRemainder P S c` is bounded by
   `−(∑_{p ∈ P} E_p − ((∑_{p ∈ P} w_p)² − ∑_{p ∈ P} w_p²)) ∑_{a ∈ S} c(a)²` and by
   `−(∑_{p ∈ P} (E_p − (|P| − 1) w_p²)) ∑_{a ∈ S} c(a)²` (`rankPResonatorRemainder_le`,
   `rankPResonatorRemainder_le_card`). Because `log r < √r` gives `2 w_r² < E_r` for every `r ≥ 2`
   (`two_mul_resonatorWeight_sq_lt_eulerEnvelope`), the remainder is negative definite for every
   prime set of rank `|P| ≤ 3` and whenever `(∑_{p ∈ P} w_p)² − ∑_{p ∈ P} w_p² < ∑_{p ∈ P} E_p`.

3. **The archimedean collar between towers (`archLevyDensity_log_div_nat`, `collarWeight`,
   `collarFormOn_eq_intra_add_cross`, `abs_intraTowerCollarForm_le`,
   `collarWeight_le_polarWeight_mul`, `disjoint_family_shift_sq_eq`).**
   Between any two Hecke cycles `1 ≤ a < b`, the narrow archimedean collar density has the exact
   algebraic value `ω(log(b/a)) = b√(ab)/(b² − a²)` (`archLevyDensity_log_div_nat`). On a `P`-smooth
   set `S`, the off-diagonal collar form `collarFormOn S c` splits identically into an
   **intra-tower collar** `intraTowerCollarForm P S c` (supported on pairs differing in one prime
   coordinate) and a **cross-tower collar** `crossTowerCollarForm P S c` (supported on pairs where
   `heckeIncidence a b = 0`, `collarFormOn_eq_intra_add_cross`). Along each prime `p`,
   `(1 / log p) τ_p(k) < ω(k log p) ≤ (p² / ((p² − 1) log p)) τ_p(k)`, so the intra-tower collar is
   bounded directly against the Euler envelopes:
   `|intraTowerCollarForm P S c| ≤ (∑_{p ∈ P} (p² / ((p² − 1) log p)) E_p) ∑_{a ∈ S} c(a)²`
   (`abs_intraTowerCollarForm_le`). Across towers, `collarWeight a b` equals `q√(pq)/(q² − p²)` at
   every anti-diagonal ratio `b/a = q/p`, is bounded pointwise by `(max(a, b)/4)(√(b/a) + √(a/b))`
   against the pole pairing (`collarWeight_le_polarWeight_mul`), and for any disjointly supported
   real bump family `{g_a}_{a ∈ S}` the total continuum collar coupling equals the diagonal Lévy
   jump self-energy minus the global jump energy of `F = ∑_{a ∈ S} c(a) g_a`, so it never exceeds
   `∑_{a ∈ S} c(a)² J_self(g_a)` (`disjoint_family_shift_sq_eq`, `disjoint_lattice_collar_le_selfJump`).

4. **Positivity decision for the finite-Euler-product form on lattice tests
   (`finiteEulerLatticeForm`, `finiteEulerLatticeForm_nonneg_of_sum_eulerEnvelope_le`,
   `exists_finiteEulerLatticeForm_box_neg_of_lt`, `collarCoupledEulerLatticeForm`,
   `collarCoupledEulerLatticeForm_nonneg`, `poleCompensatedCollarLatticeForm_nonneg`).**
   The finite-Euler-product form `finiteEulerLatticeForm S κ c = κ ∑_{a ∈ S} c(a)² − heckeFormOn S c`
   is positive semidefinite on every `P`-smooth set `S` whenever `κ ≥ ∑_{p ∈ P} E_p` (and positive
   definite when `κ > ∑_{p ∈ P} E_p`), while for any `κ < E_p + E_q` it becomes strictly negative on
   the constant resonant train of a `{p, q}`-box once `M, N` are large enough: thus `κ ≥ ∑_{p ∈ P} E_p`
   is the exact universal positivity threshold across boxes. Including the intra- and cross-tower
   collar gives the exact positivity thresholds for `collarCoupledEulerLatticeForm` and for the
   pole-compensated lattice form on effective lattice cycles.
-/

open Finset MeasureTheory Set Filter
open Zeta23 RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ## §1. The rank-`P` Cartesian / Kronecker law and additivity of Euler envelopes -/

/-- The prime-to-`p` cofactor `a / p^{v_p(a)}` of a natural number `a`. -/
def primeCofactor (p a : ℕ) : ℕ := a / p ^ (a.factorization p)

theorem primeCofactor_mul_pow (p a : ℕ) :
    primeCofactor p a * p ^ (a.factorization p) = a :=
  Nat.div_mul_cancel (Nat.ordProj_dvd a p)

theorem primeCofactor_ne_zero {p a : ℕ} (ha : a ≠ 0) : primeCofactor p a ≠ 0 := by
  intro h
  have := primeCofactor_mul_pow p a
  rw [h, zero_mul] at this
  exact ha this.symm

theorem not_dvd_primeCofactor {p a : ℕ} (hp : p.Prime) (ha : a ≠ 0) :
    ¬ p ∣ primeCofactor p a :=
  Nat.not_dvd_ordCompl hp ha

/-- The prime factorization of `primeCofactor p a` vanishes at `p` and agrees with `a` off `p`. -/
theorem factorization_primeCofactor {p a : ℕ} (hp : p.Prime) (_ha : a ≠ 0) (r : ℕ) :
    (primeCofactor p a).factorization r = if r = p then 0 else a.factorization r := by
  have hdvd : p ^ (a.factorization p) ∣ a := Nat.ordProj_dvd a p
  have hdiv := congrArg (fun f => f r) (Nat.factorization_div hdvd)
  simp only [primeCofactor, Finsupp.tsub_apply, hp.factorization_pow, Finsupp.single_apply] at hdiv ⊢
  rw [hdiv]
  by_cases hr : r = p
  · subst hr; simp
  · rw [if_neg (Ne.symm hr), if_neg hr, Nat.sub_zero]

/-- Two positive integers have the same prime-to-`p` cofactor iff their exponent vectors agree at
every prime `r ≠ p`. -/
theorem primeCofactor_eq_iff_factorization_eq_off {p a b : ℕ} (hp : p.Prime)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    primeCofactor p a = primeCofactor p b ↔ ∀ r, r ≠ p → a.factorization r = b.factorization r := by
  constructor
  · intro h r hr
    have hfac := congrArg (fun n : ℕ => n.factorization r) h
    rw [factorization_primeCofactor hp ha r, factorization_primeCofactor hp hb r,
      if_neg hr, if_neg hr] at hfac
    exact hfac
  · intro h
    apply Nat.eq_of_factorization_eq (primeCofactor_ne_zero ha) (primeCofactor_ne_zero hb)
    intro r
    rw [factorization_primeCofactor hp ha r, factorization_primeCofactor hp hb r]
    by_cases hr : r = p
    · simp [hr]
    · rw [if_neg hr, if_neg hr, h r hr]

/-- If `primeCofactor p a = primeCofactor p b` and `primeCofactor q a = primeCofactor q b` for two
distinct primes `p ≠ q`, then `a = b`. -/
theorem eq_of_primeCofactor_eq_of_ne {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha : a ≠ 0) (hb : b ≠ 0) (hpa : primeCofactor p a = primeCofactor p b)
    (hqa : primeCofactor q a = primeCofactor q b) : a = b := by
  apply Nat.eq_of_factorization_eq ha hb
  intro r
  by_cases hrp : r = p
  · subst hrp
    exact (primeCofactor_eq_iff_factorization_eq_off hq ha hb).mp hqa r hpq
  · exact (primeCofactor_eq_iff_factorization_eq_off hp ha hb).mp hpa r hrp

/-- **The rank-`P` Cartesian decomposition of Hecke incidence.** For any finite set `P` of primes
and any positive integers `a, b` whose factorizations agree outside `P`, the Hecke incidence is the
sum over `p ∈ P` of the single-prime tower weights along the `p`-fibres
`primeCofactor p a = primeCofactor p b`. -/
theorem heckeIncidence_eq_sum_primes {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hout : ∀ r, r ∉ P → a.factorization r = b.factorization r) :
    heckeIncidence a b = ∑ p ∈ P,
      if primeCofactor p a = primeCofactor p b then
        towerWeight p (Nat.dist (a.factorization p) (b.factorization p))
      else 0 := by
  by_cases hab : a = b
  · subst hab
    rw [heckeIncidence, ratioIncidence, if_pos (dvd_refl a), Nat.div_self (Nat.pos_of_ne_zero ha)]
    simp [primeAtom, towerWeight_zero]
  · by_cases hex : ∃ p ∈ P, primeCofactor p a = primeCofactor p b
    · rcases hex with ⟨p₀, hp₀P, hp₀eq⟩
      have hp₀ : p₀.Prime := hP p₀ hp₀P
      have hoff := (primeCofactor_eq_iff_factorization_eq_off hp₀ ha hb).mp hp₀eq
      rw [heckeIncidence_eq_towerWeight ha hb hp₀ hoff]
      rw [Finset.sum_eq_single p₀]
      · rw [if_pos hp₀eq]
      · intro q hqP hqp₀
        rw [if_neg]
        intro hqeq
        exact hab (eq_of_primeCofactor_eq_of_ne hp₀ (hP q hqP) hqp₀.symm ha hb hp₀eq hqeq)
      · intro hp₀_not; exact absurd hp₀P hp₀_not
    · push Not at hex
      rw [Finset.sum_eq_zero (fun p hp => by rw [if_neg (hex p hp)])]
      refine heckeIncidence_eq_zero ha hb fun p hp => ?_
      by_cases hpP : p ∈ P
      · have hne : ¬ ∀ r, r ≠ p → a.factorization r = b.factorization r := by
          intro hall
          exact hex p hpP ((primeCofactor_eq_iff_factorization_eq_off hp ha hb).mpr hall)
        push Not at hne
        exact hne
      · have hne_ab : ∃ r, a.factorization r ≠ b.factorization r := by
          by_contra hall
          push Not at hall
          exact hab (Nat.eq_of_factorization_eq ha hb hall)
        rcases hne_ab with ⟨r, hrne⟩
        have hrP : r ∈ P := by
          by_contra hrnot
          exact hrne (hout r hrnot)
        exact ⟨r, fun hrp => hpP (hrp ▸ hrP), hrne⟩

/-- On `P`-smooth positive integers (`a.primeFactors ⊆ P`, `b.primeFactors ⊆ P`), the Hecke
incidence is the sum over `p ∈ P` of the single-prime tower weights. -/
theorem heckeIncidence_eq_sum_primes_of_primeFactors_subset {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (haP : a.primeFactors ⊆ P) (hbP : b.primeFactors ⊆ P) :
    heckeIncidence a b = ∑ p ∈ P,
      if primeCofactor p a = primeCofactor p b then
        towerWeight p (Nat.dist (a.factorization p) (b.factorization p))
      else 0 := by
  refine heckeIncidence_eq_sum_primes hP ha hb fun r hr => ?_
  have har : a.factorization r = 0 := by
    by_contra hne
    exact hr (haP (Nat.support_factorization a ▸ Finsupp.mem_support_iff.mpr hne))
  have hbr : b.factorization r = 0 := by
    by_contra hne
    exact hr (hbP (Nat.support_factorization b ▸ Finsupp.mem_support_iff.mpr hne))
  rw [har, hbr]

/-- The Hecke quadratic form on an arbitrary finite set of positive integers `S` with coefficients
`c : ℕ → ℝ`. -/
def heckeFormOn (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ S, c a * c b * heckeIncidence a b

/-- The `p`-slice of the Hecke quadratic form on `S`: pairs in `S` sharing the same prime-to-`p`
cofactor interact with the single-prime tower weight `τ_p(|v_p(a) − v_p(b)|)`. -/
def primeSliceForm (p : ℕ) (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ S,
    if primeCofactor p a = primeCofactor p b then
      c a * c b * towerWeight p (Nat.dist (a.factorization p) (b.factorization p))
    else 0

/-- **The rank-`P` Kronecker law on any finite `P`-smooth support.** The Hecke quadratic form on any
finite set `S` of positive `P`-smooth integers is the sum over `p ∈ P` of the single-prime slice
forms `primeSliceForm p S c`; there is no cross-prime prime coupling. -/
theorem heckeFormOn_eq_sum_primeSliceForm {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ a ∈ S, a ≠ 0 ∧ a.primeFactors ⊆ P) (c : ℕ → ℝ) :
    heckeFormOn S c = ∑ p ∈ P, primeSliceForm p S c := by
  unfold heckeFormOn primeSliceForm
  have hterm : ∀ a ∈ S, ∀ b ∈ S,
      c a * c b * heckeIncidence a b = ∑ p ∈ P,
        if primeCofactor p a = primeCofactor p b then
          c a * c b * towerWeight p (Nat.dist (a.factorization p) (b.factorization p))
        else 0 := by
    intro a ha b hb
    rw [heckeIncidence_eq_sum_primes_of_primeFactors_subset hP (hS a ha).1 (hS b hb).1
      (hS a ha).2 (hS b hb).2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl (hterm a ha)]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]

/-- Along any single `p`-fibre `{b ∈ S : primeCofactor p b = primeCofactor p a}`, the row sum of
the tower weights is bounded by the Euler envelope `E_p = 2 log p/(√p − 1)`. -/
theorem sum_primeSlice_towerWeight_le {p : ℕ} (hp : p.Prime) {S : Finset ℕ}
    {a : ℕ} (_ha : a ∈ S) :
    (∑ b ∈ S, if primeCofactor p a = primeCofactor p b then
        towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) else 0) ≤
      eulerEnvelope p := by
  generalize hM : S.sup (fun x => x.factorization p) + 1 = M
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn (fun b : ℕ => b.factorization p)
      (S.filter (fun b => primeCofactor p a = primeCofactor p b) : Finset ℕ) := by
    intro b₁ hb₁ b₂ hb₂ hfac
    dsimp only at hfac
    have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hb₁)).2
    have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hb₂)).2
    rw [← primeCofactor_mul_pow p b₁, ← primeCofactor_mul_pow p b₂, ← h1, ← h2, hfac]
  have hsub : (S.filter (fun b => primeCofactor p a = primeCofactor p b)).image
      (fun b => b.factorization p) ⊆ range M := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨b, hb, rfl⟩
    have hbS := (Finset.mem_filter.mp hb).1
    rw [Finset.mem_range, ← hM]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun x : ℕ => x.factorization p) hbS)
  have himg : ∑ b ∈ S.filter (fun b => primeCofactor p a = primeCofactor p b),
        towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) =
      ∑ i' ∈ (S.filter (fun b => primeCofactor p a = primeCofactor p b)).image
          (fun b => b.factorization p), towerWeight p (Nat.dist (a.factorization p) i') :=
    (Finset.sum_image (f := fun i' => towerWeight p (Nat.dist (a.factorization p) i')) hinj).symm
  calc ∑ b ∈ S.filter (fun b => primeCofactor p a = primeCofactor p b),
        towerWeight p (Nat.dist (a.factorization p) (b.factorization p))
      = ∑ i' ∈ (S.filter (fun b => primeCofactor p a = primeCofactor p b)).image
          (fun b => b.factorization p), towerWeight p (Nat.dist (a.factorization p) i') := himg
    _ ≤ ∑ i' ∈ range M, towerWeight p (Nat.dist (a.factorization p) i') :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => towerWeight_nonneg _ _)
    _ ≤ 2 * (Real.log p / (Real.sqrt p - 1)) := sum_towerWeight_dist_le hp M (a.factorization p)
    _ = eulerEnvelope p := by unfold eulerEnvelope; ring

/-- **Schur bound on a single prime slice.** For any prime `p` and any finite set `S ⊂ ℕ`,
`|primeSliceForm p S c| ≤ E_p ∑_{a ∈ S} c(a)²`. -/
theorem abs_primeSliceForm_le {p : ℕ} (hp : p.Prime) (S : Finset ℕ) (c : ℕ → ℝ) :
    |primeSliceForm p S c| ≤ eulerEnvelope p * ∑ a ∈ S, c a ^ 2 := by
  have hterm : ∀ a ∈ S, ∀ b ∈ S,
      |if primeCofactor p a = primeCofactor p b then
          c a * c b * towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) else 0| ≤
        (c a ^ 2 / 2 + c b ^ 2 / 2) *
          (if primeCofactor p a = primeCofactor p b then
            towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) else 0) := by
    intro a _ b _
    split_ifs
    · rw [abs_mul, abs_of_nonneg (towerWeight_nonneg _ _), abs_mul]
      have hab : |c a| * |c b| ≤ c a ^ 2 / 2 + c b ^ 2 / 2 := by
        nlinarith [sq_nonneg (|c a| - |c b|), sq_abs (c a), sq_abs (c b)]
      exact mul_le_mul_of_nonneg_right hab (towerWeight_nonneg _ _)
    · simp
  have hsym : ∑ a ∈ S, ∑ b ∈ S,
      (c a ^ 2 / 2 + c b ^ 2 / 2) *
        (if primeCofactor p a = primeCofactor p b then
          towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) else 0) =
      ∑ a ∈ S, c a ^ 2 * ∑ b ∈ S,
        (if primeCofactor p a = primeCofactor p b then
          towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) else 0) := by
    simp only [add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun a b => c b ^ 2 / 2 *
      if primeCofactor p a = primeCofactor p b then
        towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) else 0)]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Nat.dist_comm (b.factorization p) (a.factorization p)]
    by_cases h : primeCofactor p a = primeCofactor p b
    · rw [if_pos h, if_pos h.symm]; ring
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  calc |primeSliceForm p S c|
      ≤ ∑ a ∈ S, ∑ b ∈ S, |if primeCofactor p a = primeCofactor p b then
          c a * c b * towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) else 0| := by
        unfold primeSliceForm
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ =>
          Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a ∈ S, ∑ b ∈ S, (c a ^ 2 / 2 + c b ^ 2 / 2) *
          (if primeCofactor p a = primeCofactor p b then
            towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) else 0) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hterm a ha b hb
    _ = ∑ a ∈ S, c a ^ 2 * ∑ b ∈ S,
          (if primeCofactor p a = primeCofactor p b then
            towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) else 0) := hsym
    _ ≤ ∑ a ∈ S, c a ^ 2 * eulerEnvelope p :=
        Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left
          (sum_primeSlice_towerWeight_le hp ha) (sq_nonneg _)
    _ = eulerEnvelope p * ∑ a ∈ S, c a ^ 2 := by rw [← Finset.sum_mul, mul_comm]

/-- **The Euler envelopes add on any `P`-smooth support.** For any finite set `P` of primes and any
finite set `S` of positive `P`-smooth integers,
`|heckeFormOn S c| ≤ (∑_{p ∈ P} E_p) ∑_{a ∈ S} c(a)²`. -/
theorem abs_heckeFormOn_le_sum_eulerEnvelope {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ a ∈ S, a ≠ 0 ∧ a.primeFactors ⊆ P) (c : ℕ → ℝ) :
    |heckeFormOn S c| ≤ (∑ p ∈ P, eulerEnvelope p) * ∑ a ∈ S, c a ^ 2 := by
  rw [heckeFormOn_eq_sum_primeSliceForm hP hS c, Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun p hp => abs_primeSliceForm_le (hP p hp) S c)

/-- Inductive product box: given a base set `B` of positive integers coprime to `p` and a tower
length `M`, `towerProductBox B p M = {m * p^i : m ∈ B, i < M}`. -/
def towerProductBox (B : Finset ℕ) (p M : ℕ) : Finset ℕ :=
  (B ×ˢ range M).image (fun x => x.1 * p ^ x.2)

theorem factorization_mul_pow_prime_of_not_dvd {m p : ℕ} (hp : p.Prime) (hm0 : m ≠ 0)
    (hpm : ¬ p ∣ m) (i : ℕ) :
    (m * p ^ i).factorization p = i ∧ primeCofactor p (m * p ^ i) = m := by
  have hfac_m : m.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpm
  have hfac : (m * p ^ i).factorization p = i := by
    rw [Nat.factorization_mul hm0 (pow_ne_zero i hp.ne_zero), Finsupp.add_apply, hfac_m, zero_add,
      hp.factorization_pow, Finsupp.single_eq_same]
  refine ⟨hfac, ?_⟩
  rw [primeCofactor, hfac, Nat.mul_div_cancel _ (pow_pos hp.pos i)]

theorem injOn_towerProductBox {B : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (hB : ∀ m ∈ B, m ≠ 0 ∧ ¬ p ∣ m) (M : ℕ) :
    Set.InjOn (fun x : ℕ × ℕ => x.1 * p ^ x.2) (B ×ˢ range M : Finset (ℕ × ℕ)) := by
  intro x hx y hy hxy
  rcases Finset.mem_product.mp (Finset.mem_coe.mp hx) with ⟨hxB, _⟩
  rcases Finset.mem_product.mp (Finset.mem_coe.mp hy) with ⟨hyB, _⟩
  have hx1 := factorization_mul_pow_prime_of_not_dvd hp (hB x.1 hxB).1 (hB x.1 hxB).2 x.2
  have hy1 := factorization_mul_pow_prime_of_not_dvd hp (hB y.1 hyB).1 (hB y.1 hyB).2 y.2
  have hi : x.2 = y.2 := by
    have := congrArg (fun n : ℕ => n.factorization p) hxy
    simp only [hx1.1, hy1.1] at this
    exact this
  have hm : x.1 = y.1 := by
    have := congrArg (primeCofactor p) hxy
    simp only [hx1.2, hy1.2] at this
    exact this
  exact Prod.ext hm hi

theorem card_towerProductBox {B : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (hB : ∀ m ∈ B, m ≠ 0 ∧ ¬ p ∣ m) (M : ℕ) :
    (towerProductBox B p M).card = B.card * M := by
  rw [towerProductBox, Finset.card_image_of_injOn (injOn_towerProductBox hp hB M),
    Finset.card_product, Finset.card_range]

/-- **The `p`-slice of an inductive product box is the sum of single-prime tower forms over the
base `B`.** -/
theorem primeSliceForm_towerProductBox_self {B : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (hB : ∀ m ∈ B, m ≠ 0 ∧ ¬ p ∣ m) (M : ℕ) (c : ℕ → ℝ) :
    primeSliceForm p (towerProductBox B p M) c =
      ∑ m ∈ B, towerForm p M (fun i => c (m * p ^ i)) := by
  unfold primeSliceForm towerProductBox towerForm
  have hinj := injOn_towerProductBox hp hB M
  rw [Finset.sum_image hinj]
  have hinner : ∀ x ∈ B ×ˢ range M,
      (∑ b ∈ (B ×ˢ range M).image (fun y : ℕ × ℕ => y.1 * p ^ y.2),
        if primeCofactor p (x.1 * p ^ x.2) = primeCofactor p b then
          c (x.1 * p ^ x.2) * c b *
            towerWeight p (Nat.dist ((x.1 * p ^ x.2).factorization p) (b.factorization p))
        else 0) =
      ∑ y ∈ B ×ˢ range M,
        if x.1 = y.1 then
          c (x.1 * p ^ x.2) * c (y.1 * p ^ y.2) * towerWeight p (Nat.dist x.2 y.2)
        else 0 := by
    intro x hx
    rw [Finset.sum_image hinj]
    rcases Finset.mem_product.mp hx with ⟨hxB, _⟩
    have hx_prop := factorization_mul_pow_prime_of_not_dvd hp (hB x.1 hxB).1 (hB x.1 hxB).2 x.2
    refine Finset.sum_congr rfl fun y hy => ?_
    rcases Finset.mem_product.mp hy with ⟨hyB, _⟩
    have hy_prop := factorization_mul_pow_prime_of_not_dvd hp (hB y.1 hyB).1 (hB y.1 hyB).2 y.2
    rw [hx_prop.1, hx_prop.2, hy_prop.1, hy_prop.2]
  rw [Finset.sum_congr rfl hinner, Finset.sum_product]
  refine Finset.sum_congr rfl fun m hm => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_product]
  rw [Finset.sum_eq_single m]
  · simp
  · intro m' _ hm'
    exact Finset.sum_eq_zero fun i' _ => by rw [if_neg (Ne.symm hm')]
  · intro hm_not; exact absurd hm hm_not

/-- On the constant vector `c ≡ 1`, the `p`-slice of `towerProductBox B p M` equals
`B.card * towerForm p M (fun _ => 1)`. -/
theorem primeSliceForm_towerProductBox_one {B : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (hB : ∀ m ∈ B, m ≠ 0 ∧ ¬ p ∣ m) (M : ℕ) :
    primeSliceForm p (towerProductBox B p M) (fun _ => 1) =
      B.card * towerForm p M (fun _ => 1) := by
  rw [primeSliceForm_towerProductBox_self hp hB M]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- Exact closed form of the partial geometric sum of tower weights:
`∑_{k < K} τ_p(k + 1) = (log p / (√p − 1)) (1 − p^{−K/2})`. -/
theorem sum_towerWeight_eq {p : ℕ} (hp : p.Prime) (K : ℕ) :
    ∑ k ∈ range K, towerWeight p (k + 1) =
      (Real.log p / (Real.sqrt p - 1)) * (1 - (1 / Real.sqrt p) ^ K) := by
  have hs : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by exact_mod_cast hp.one_lt)
  set z := 1 / Real.sqrt p
  have hz1 : z < 1 := by rw [div_lt_one (by linarith)]; exact hs
  have hterm : ∀ k ∈ range K, towerWeight p (k + 1) = Real.log p * z * z ^ k := fun k _ => by
    rw [towerWeight_eq_geom hp (by omega), pow_succ]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have h1 : (1 - z) * ∑ k ∈ range K, z ^ k = 1 - z ^ K := mul_neg_geom_sum z K
  have hgeom : ∑ k ∈ range K, z ^ k = (1 - z ^ K) / (1 - z) := by
    rw [eq_div_iff (by linarith), mul_comm, h1]
  rw [hgeom]
  simp only [z]
  field_simp

/-- Lower bound on `towerForm p M (fun _ => 1)` by truncating at `K ≤ M`:
`2 (M − K) ∑_{k < K} τ_p(k + 1) ≤ towerForm p M (fun _ => 1)`. -/
theorem two_mul_sub_mul_sum_towerWeight_le_towerForm_one {p M K : ℕ} (hKM : K ≤ M) :
    2 * ((M - K : ℕ) : ℝ) * ∑ k ∈ range K, towerWeight p (k + 1) ≤
      towerForm p M (fun _ => 1) := by
  rw [towerForm_one, mul_assoc, Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (Finset.sum_le_sum fun k hk => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hKM) fun k _ _ =>
      mul_nonneg (Nat.cast_nonneg _) (towerWeight_nonneg _ _))
  have hkK := Finset.mem_range.mp hk
  refine mul_le_mul_of_nonneg_right ?_ (towerWeight_nonneg _ _)
  exact_mod_cast (by omega : M - K ≤ M - 1 - k)

/-- **The resonant train attains the Euler envelope asymptotically.** For every prime `p` and every
constant `c < E_p`, there exists a tower length `M ≥ 1` such that `c * M < towerForm p M (fun _ => 1)`. -/
theorem exists_towerForm_one_gt_of_lt_eulerEnvelope {p : ℕ} (hp : p.Prime) {c : ℝ}
    (hc : c < eulerEnvelope p) :
    ∃ M : ℕ, 1 ≤ M ∧ c * (M : ℝ) < towerForm p M (fun _ => 1) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hs : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hlog : 0 < Real.log p := Real.log_pos (by linarith)
  have hE : 0 < eulerEnvelope p := by unfold eulerEnvelope; positivity
  set c' := max c 0
  have hc'0 : 0 ≤ c' := le_max_right c 0
  have hcc' : c ≤ c' := le_max_left c 0
  have hc'E : c' < eulerEnvelope p := max_lt hc hE
  set z := 1 / Real.sqrt p
  have hz0 : 0 ≤ z := by positivity
  have hz1 : z < 1 := by rw [div_lt_one (by linarith)]; exact hs
  set δ := (eulerEnvelope p - c') / (2 * eulerEnvelope p)
  have hδ : 0 < δ := div_pos (by linarith) (by positivity)
  have hδ_le : δ ≤ 1 / 2 := by
    simp only [δ]
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hpow : Tendsto (fun K : ℕ => z ^ K) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hz0 hz1
  obtain ⟨K, hK1, hKz⟩ := ((eventually_ge_atTop 1).and (hpow.eventually (gt_mem_nhds hδ))).exists
  obtain ⟨M, hM⟩ := exists_nat_gt (max (K : ℝ) ((K : ℝ) / δ))
  have hKM : K ≤ M := by
    have : (K : ℝ) < M := lt_of_le_of_lt (le_max_left _ _) hM
    exact_mod_cast this.le
  have hM1 : 1 ≤ M := le_trans hK1 hKM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hKdiv : (K : ℝ) < δ * M := by
    have : (K : ℝ) / δ < M := lt_of_le_of_lt (le_max_right _ _) hM
    rwa [div_lt_iff₀ hδ, mul_comm] at this
  refine ⟨M, hM1, ?_⟩
  have hlo := two_mul_sub_mul_sum_towerWeight_le_towerForm_one (p := p) hKM
  rw [sum_towerWeight_eq hp K] at hlo
  have hsub : ((M - K : ℕ) : ℝ) = (M : ℝ) - K := Nat.cast_sub hKM
  have hrew : 2 * ((M - K : ℕ) : ℝ) * ((Real.log p / (Real.sqrt p - 1)) * (1 - z ^ K)) =
      ((M : ℝ) - K) * eulerEnvelope p * (1 - z ^ K) := by
    rw [hsub]; unfold eulerEnvelope; ring
  rw [hrew] at hlo
  have h1 : (1 - δ) * (M : ℝ) < (M : ℝ) - K := by linarith
  have h2 : 1 - δ < 1 - z ^ K := by linarith [show z ^ K < δ from hKz]
  have h1_pos : 0 < 1 - δ := by linarith
  have hMK_pos : 0 < (M : ℝ) - K := lt_trans (mul_pos h1_pos hMpos) h1
  have hprod : (1 - δ) * (M : ℝ) * eulerEnvelope p * (1 - δ) <
      ((M : ℝ) - K) * eulerEnvelope p * (1 - z ^ K) := by
    have ha : (1 - δ) * (M : ℝ) * eulerEnvelope p < ((M : ℝ) - K) * eulerEnvelope p :=
      mul_lt_mul_of_pos_right h1 hE
    exact mul_lt_mul ha h2.le h1_pos (mul_pos hMK_pos hE).le
  have hc'_eq : c' * (M : ℝ) = (1 - 2 * δ) * (M : ℝ) * eulerEnvelope p := by
    simp only [δ]
    field_simp [hE.ne']
    ring
  have hsq : (1 - 2 * δ) * (M : ℝ) * eulerEnvelope p <
      (1 - δ) * (M : ℝ) * eulerEnvelope p * (1 - δ) := by
    have : (1 - δ) * (M : ℝ) * eulerEnvelope p * (1 - δ) -
        (1 - 2 * δ) * (M : ℝ) * eulerEnvelope p = δ ^ 2 * (M : ℝ) * eulerEnvelope p := by ring
    linarith [mul_pos (mul_pos (sq_pos_of_pos hδ) hMpos) hE]
  calc c * (M : ℝ) ≤ c' * (M : ℝ) := mul_le_mul_of_nonneg_right hcc' hMpos.le
    _ = (1 - 2 * δ) * (M : ℝ) * eulerEnvelope p := hc'_eq
    _ < (1 - δ) * (M : ℝ) * eulerEnvelope p * (1 - δ) := hsq
    _ < ((M : ℝ) - K) * eulerEnvelope p * (1 - z ^ K) := hprod
    _ ≤ towerForm p M (fun _ => 1) := hlo

/-- **On a `{p, q}`-box the bi-lattice train attains `E_p + E_q` asymptotically.** For any distinct
primes `p ≠ q` and any `κ < E_p + E_q`, there exist box sizes `M, N ≥ 1` such that
`κ * (M * N) < heckeForm p q M N (fun _ => 1)`. -/
theorem exists_heckeForm_box_one_gt_of_lt_add_eulerEnvelope {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) {κ : ℝ} (hκ : κ < eulerEnvelope p + eulerEnvelope q) :
    ∃ M N : ℕ, 1 ≤ M ∧ 1 ≤ N ∧
      κ * ((M : ℝ) * N) < heckeForm p q M N (fun _ => 1) := by
  set ε := (eulerEnvelope p + eulerEnvelope q - κ) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  obtain ⟨M, hM1, hM⟩ := exists_towerForm_one_gt_of_lt_eulerEnvelope hp
    (c := eulerEnvelope p - ε) (by linarith)
  obtain ⟨N, hN1, hN⟩ := exists_towerForm_one_gt_of_lt_eulerEnvelope hq
    (c := eulerEnvelope q - ε) (by linarith)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  refine ⟨M, N, hM1, hN1, ?_⟩
  rw [heckeForm_box_one hp hq hpq M N]
  have h1 := mul_lt_mul_of_pos_left hM hNpos
  have h2 := mul_lt_mul_of_pos_left hN hMpos
  have hκ_eq : κ * ((M : ℝ) * N) =
      (N : ℝ) * ((eulerEnvelope p - ε) * M) + (M : ℝ) * ((eulerEnvelope q - ε) * N) := by
    simp only [ε]; ring
  linarith

/-! ## §2. The rank-`P` resonator remainder and the sub-envelope regime -/

/-- The anti-diagonal cross-lag quadratic form between primes `p` and `q` on a finite set `S`:
`crossLagOn p q S c = ∑_{a, b ∈ S, a * q = b * p} c(a) c(b)`. -/
def crossLagOn (p q : ℕ) (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ S, if a * q = b * p then c a * c b else 0

/-- For any `p, q > 0` and any finite set `S ⊂ ℕ`, `|crossLagOn p q S c| ≤ ∑_{a ∈ S} c(a)²`. -/
theorem abs_crossLagOn_le {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (S : Finset ℕ) (c : ℕ → ℝ) :
    |crossLagOn p q S c| ≤ ∑ a ∈ S, c a ^ 2 := by
  have hrow : ∀ a ∈ S, (∑ b ∈ S, if a * q = b * p then (1 : ℝ) else 0) ≤ 1 := by
    intro a _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : (S.filter (fun b => a * q = b * p)).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun b₁ hb₁ b₂ hb₂ => ?_
      have h1 := (Finset.mem_filter.mp hb₁).2
      have h2 := (Finset.mem_filter.mp hb₂).2
      exact Nat.eq_of_mul_eq_mul_right hp (h1.symm.trans h2)
    exact_mod_cast hcard
  have hcol : ∀ b ∈ S, (∑ a ∈ S, if a * q = b * p then (1 : ℝ) else 0) ≤ 1 := by
    intro b _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : (S.filter (fun a => a * q = b * p)).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun a₁ ha₁ a₂ ha₂ => ?_
      have h1 := (Finset.mem_filter.mp ha₁).2
      have h2 := (Finset.mem_filter.mp ha₂).2
      exact Nat.eq_of_mul_eq_mul_right hq (h1.trans h2.symm)
    exact_mod_cast hcard
  have hterm : ∀ a ∈ S, ∀ b ∈ S,
      |if a * q = b * p then c a * c b else 0| ≤
        (c a ^ 2 / 2 + c b ^ 2 / 2) * (if a * q = b * p then 1 else 0) := by
    intro a _ b _
    split_ifs
    · rw [mul_one, abs_mul]
      nlinarith [sq_nonneg (|c a| - |c b|), sq_abs (c a), sq_abs (c b)]
    · simp
  calc |crossLagOn p q S c|
      ≤ ∑ a ∈ S, ∑ b ∈ S, |if a * q = b * p then c a * c b else 0| := by
        unfold crossLagOn
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ =>
          Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a ∈ S, ∑ b ∈ S, (c a ^ 2 / 2 + c b ^ 2 / 2) * (if a * q = b * p then 1 else 0) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hterm a ha b hb
    _ = (∑ a ∈ S, (c a ^ 2 / 2) * ∑ b ∈ S, if a * q = b * p then (1 : ℝ) else 0) +
          ∑ b ∈ S, (c b ^ 2 / 2) * ∑ a ∈ S, if a * q = b * p then (1 : ℝ) else 0 := by
        simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
    _ ≤ (∑ a ∈ S, (c a ^ 2 / 2) * 1) + ∑ b ∈ S, (c b ^ 2 / 2) * 1 := by
        refine add_le_add (Finset.sum_le_sum fun a ha =>
            mul_le_mul_of_nonneg_left (hrow a ha) (by positivity))
          (Finset.sum_le_sum fun b hb =>
            mul_le_mul_of_nonneg_left (hcol b hb) (by positivity))
    _ = ∑ a ∈ S, c a ^ 2 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => by ring

/-- The rank-`P` resonator remainder on a finite set `S`:
`rankPResonatorRemainder P S c = ∑_{p ∈ P} ∑_{q ∈ P \ {p}} w_p w_q crossLagOn p q S c − (∑_{p ∈ P} E_p) ∑_{a ∈ S} c(a)²`. -/
def rankPResonatorRemainder (P S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  (∑ p ∈ P, ∑ q ∈ P.erase p, resonatorWeight p * resonatorWeight q * crossLagOn p q S c) -
    (∑ p ∈ P, eulerEnvelope p) * ∑ a ∈ S, c a ^ 2

/-- **Universal upper bound on the rank-`P` resonator remainder.** -/
theorem rankPResonatorRemainder_le {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) (S : Finset ℕ)
    (c : ℕ → ℝ) :
    rankPResonatorRemainder P S c ≤
      -((∑ p ∈ P, eulerEnvelope p) -
        ((∑ p ∈ P, resonatorWeight p) ^ 2 - ∑ p ∈ P, resonatorWeight p ^ 2)) *
        ∑ a ∈ S, c a ^ 2 := by
  have hcross : ∑ p ∈ P, ∑ q ∈ P.erase p,
      resonatorWeight p * resonatorWeight q * crossLagOn p q S c ≤
      ((∑ p ∈ P, resonatorWeight p) ^ 2 - ∑ p ∈ P, resonatorWeight p ^ 2) * ∑ a ∈ S, c a ^ 2 := by
    have hterm : ∀ p ∈ P, ∀ q ∈ P.erase p,
        resonatorWeight p * resonatorWeight q * crossLagOn p q S c ≤
          resonatorWeight p * resonatorWeight q * ∑ a ∈ S, c a ^ 2 := by
      intro p hp q hq
      have hp2 := hP p hp
      have hq2 := hP q (Finset.mem_of_mem_erase hq)
      have hw : 0 ≤ resonatorWeight p * resonatorWeight q :=
        mul_nonneg (resonatorWeight_nonneg (by omega)) (resonatorWeight_nonneg (by omega))
      exact mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (abs_crossLagOn_le (by omega) (by omega) S c)) hw
    calc ∑ p ∈ P, ∑ q ∈ P.erase p, resonatorWeight p * resonatorWeight q * crossLagOn p q S c
        ≤ ∑ p ∈ P, ∑ q ∈ P.erase p, resonatorWeight p * resonatorWeight q * ∑ a ∈ S, c a ^ 2 :=
          Finset.sum_le_sum fun p hp => Finset.sum_le_sum (hterm p hp)
      _ = (∑ p ∈ P, ∑ q ∈ P.erase p, resonatorWeight p * resonatorWeight q) * ∑ a ∈ S, c a ^ 2 := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_mul]
      _ = ((∑ p ∈ P, resonatorWeight p) ^ 2 - ∑ p ∈ P, resonatorWeight p ^ 2) * ∑ a ∈ S, c a ^ 2 := by
          congr 1
          have hrow : ∀ p ∈ P, ∑ q ∈ P.erase p, resonatorWeight p * resonatorWeight q =
              resonatorWeight p * (∑ q ∈ P, resonatorWeight q) - resonatorWeight p ^ 2 := by
            intro p hp
            rw [Finset.mul_sum, ← Finset.sum_erase_add _ _ hp]
            ring
          rw [Finset.sum_congr rfl hrow, Finset.sum_sub_distrib, ← Finset.sum_mul, sq]
  unfold rankPResonatorRemainder
  linarith

/-- Whenever `(∑_{p ∈ P} w_p)² − ∑_{p ∈ P} w_p² < ∑_{p ∈ P} E_p`, the rank-`P` resonator remainder
is strictly negative on every nonzero coefficient vector. -/
theorem rankPResonatorRemainder_neg_of_subEnvelope {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p)
    (hsub : (∑ p ∈ P, resonatorWeight p) ^ 2 - ∑ p ∈ P, resonatorWeight p ^ 2 <
      ∑ p ∈ P, eulerEnvelope p)
    {S : Finset ℕ} {c : ℕ → ℝ} (hc : 0 < ∑ a ∈ S, c a ^ 2) :
    rankPResonatorRemainder P S c < 0 := by
  have hle := rankPResonatorRemainder_le hP S c
  nlinarith

/-- Cauchy–Schwarz bound on the rank-`P` resonator remainder in terms of `|P| - 1`:
`rankPResonatorRemainder P S c ≤ −(∑_{p ∈ P} (E_p − (|P| − 1) w_p²)) ∑_{a ∈ S} c(a)²`. -/
theorem rankPResonatorRemainder_le_card {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p)
    (S : Finset ℕ) (c : ℕ → ℝ) :
    rankPResonatorRemainder P S c ≤
      -(∑ p ∈ P, (eulerEnvelope p - ((P.card : ℝ) - 1) * resonatorWeight p ^ 2)) *
        ∑ a ∈ S, c a ^ 2 := by
  have hcs : (∑ p ∈ P, resonatorWeight p) ^ 2 ≤ (P.card : ℝ) * ∑ p ∈ P, resonatorWeight p ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := P) (f := resonatorWeight)
  have h1 := rankPResonatorRemainder_le hP S c
  have hE : 0 ≤ ∑ a ∈ S, c a ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hrew : ∑ p ∈ P, (eulerEnvelope p - ((P.card : ℝ) - 1) * resonatorWeight p ^ 2) =
      (∑ p ∈ P, eulerEnvelope p) - ((P.card : ℝ) * (∑ p ∈ P, resonatorWeight p ^ 2) -
        ∑ p ∈ P, resonatorWeight p ^ 2) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hrew]
  nlinarith [mul_le_mul_of_nonneg_right hcs hE]

/-- `log x < √x` for every `x > 0`. -/
theorem log_lt_sqrt_of_pos {x : ℝ} (hx : 0 < x) : Real.log x < Real.sqrt x := by
  have hs : 0 < Real.sqrt x / 2 := by positivity
  have h := Real.log_le_sub_one_of_pos hs
  rw [Real.log_div (Real.sqrt_pos.mpr hx).ne' (by norm_num), Real.log_sqrt hx.le] at h
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  linarith

/-- **Twice the square of the comb weight is strictly below the Euler envelope**:
`2 w_r² < E_r` for every `r ≥ 2`. -/
theorem two_mul_resonatorWeight_sq_lt_eulerEnvelope {r : ℕ} (hr : 2 ≤ r) :
    2 * resonatorWeight r ^ 2 < eulerEnvelope r := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hpos : (0 : ℝ) < r := by linarith
  have hs1 : 1 < Real.sqrt r := by
    rw [Real.lt_sqrt (by norm_num)]; linarith
  have hL : 0 < Real.log r := Real.log_pos (by linarith)
  have hLs : Real.log r < Real.sqrt r := log_lt_sqrt_of_pos hpos
  unfold resonatorWeight eulerEnvelope
  rw [div_pow, ← mul_div_assoc, div_lt_div_iff₀ (by positivity) (by linarith)]
  have hsq : Real.sqrt r * Real.sqrt r = (r : ℝ) := Real.mul_self_sqrt hpos.le
  have hprod : Real.log r * (Real.sqrt r - 1) < Real.sqrt r * Real.sqrt r :=
    mul_lt_mul'' hLs (by linarith) hL.le (by linarith)
  nlinarith

/-- **Negative definiteness of the rank-`P` resonator remainder for `|P| ≤ 3`.** For any prime set
`P` with `1 ≤ |P| ≤ 3` (`∀ p ∈ P, 2 ≤ p`), `rankPResonatorRemainder P S c < 0` on every nonzero
coefficient vector (`0 < ∑_{a ∈ S} c(a)²`). -/
theorem rankPResonatorRemainder_neg_of_card_le_three {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p)
    (h1 : 1 ≤ P.card) (h3 : P.card ≤ 3) {S : Finset ℕ} {c : ℕ → ℝ}
    (hc : 0 < ∑ a ∈ S, c a ^ 2) :
    rankPResonatorRemainder P S c < 0 := by
  have hle := rankPResonatorRemainder_le_card hP S c
  have hcard_le : (P.card : ℝ) - 1 ≤ 2 := by
    have : (P.card : ℝ) ≤ 3 := by exact_mod_cast h3
    linarith
  have hpos : 0 < ∑ p ∈ P, (eulerEnvelope p - ((P.card : ℝ) - 1) * resonatorWeight p ^ 2) := by
    refine Finset.sum_pos (fun p hp => ?_) (Finset.card_pos.mp h1)
    have h2w := two_mul_resonatorWeight_sq_lt_eulerEnvelope (hP p hp)
    have hw_le : ((P.card : ℝ) - 1) * resonatorWeight p ^ 2 ≤ 2 * resonatorWeight p ^ 2 :=
      mul_le_mul_of_nonneg_right hcard_le (sq_nonneg _)
    linarith
  nlinarith

/-! ## §3. The archimedean collar between towers -/

/-- **Exact algebraic value of the archimedean collar density between any two Hecke cycles.** For
`1 ≤ a < b`, `ω(log(b/a)) = b√(ab) / (b² − a²)`. -/
theorem archLevyDensity_log_div_nat {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    archLevyDensity (Real.log ((b : ℝ) / a)) =
      (b : ℝ) * Real.sqrt ((a : ℝ) * b) / ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have ha0' := ha0.ne'
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have ht : 1 < (b : ℝ) / a := (one_lt_div ha0).mpr hab'
  have hsq : Real.sqrt ((a : ℝ) * b) = (a : ℝ) * Real.sqrt ((b : ℝ) / a) := by
    rw [show (a : ℝ) * b = (a : ℝ) ^ 2 * ((b : ℝ) / a) by field_simp,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ha0.le]
  have hba : (b : ℝ) ^ 2 - (a : ℝ) ^ 2 ≠ 0 := by nlinarith
  rw [archLevyDensity_log ht, hsq,
    show ((b : ℝ) / a) ^ 2 - 1 = ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) / (a : ℝ) ^ 2 by field_simp]
  field_simp

/-- The off-diagonal archimedean collar weight between two positive integers:
`collarWeight a b = ω(|log b − log a|)` for `a ≠ b` positive, and `0` on the diagonal or at `0`. -/
def collarWeight (a b : ℕ) : ℝ :=
  if a = b ∨ a = 0 ∨ b = 0 then 0 else archLevyDensity |Real.log b - Real.log a|

theorem collarWeight_comm (a b : ℕ) : collarWeight a b = collarWeight b a := by
  unfold collarWeight
  have heq : (a = b ∨ a = 0 ∨ b = 0) ↔ (b = a ∨ b = 0 ∨ a = 0) := by tauto
  simp only [heq, abs_sub_comm]

theorem collarWeight_self (a : ℕ) : collarWeight a a = 0 := by
  simp [collarWeight]

theorem collarWeight_nonneg (a b : ℕ) : 0 ≤ collarWeight a b := by
  unfold collarWeight
  split_ifs with h
  · exact le_rfl
  · push Not at h
    rcases h with ⟨hab, ha0, hb0⟩
    have ha_pos : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha0
    have hb_pos : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb0
    have hlog_ne : Real.log (b : ℝ) - Real.log (a : ℝ) ≠ 0 := by
      intro hsub
      have hlog_eq : Real.log (b : ℝ) = Real.log (a : ℝ) := sub_eq_zero.mp hsub
      have hba : (b : ℝ) = a := by
        have := congrArg Real.exp hlog_eq
        rwa [Real.exp_log hb_pos, Real.exp_log ha_pos] at this
      exact hab (by exact_mod_cast hba.symm)
    exact (archLevyDensity_pos (abs_pos.mpr hlog_ne)).le

/-- For `1 ≤ a < b`, `collarWeight a b = b√(ab) / (b² − a²)`. -/
theorem collarWeight_eq_of_lt {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    collarWeight a b = (b : ℝ) * Real.sqrt ((a : ℝ) * b) / ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hlog : Real.log (b : ℝ) - Real.log (a : ℝ) = Real.log ((b : ℝ) / a) :=
    (Real.log_div hb0.ne' ha0.ne').symm
  have hpos : 0 < Real.log ((b : ℝ) / a) := Real.log_pos ((one_lt_div ha0).mpr hab')
  unfold collarWeight
  rw [if_neg (by omega), hlog, abs_of_pos hpos, archLevyDensity_log_div_nat ha hab]

/-- **Two-sided comparison of the single-tower collar with the prime tower weight.** Along the
tower of a prime `p`, for every `k ≥ 1`,
`τ_p(k) / log p < ω(k log p) ≤ (p² / ((p² − 1) log p)) τ_p(k)`. -/
theorem archLevyDensity_mul_log_prime_bounds {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    towerWeight p k / Real.log p < archLevyDensity ((k : ℝ) * Real.log p) ∧
      archLevyDensity ((k : ℝ) * Real.log p) ≤
        ((p : ℝ) ^ 2 / (((p : ℝ) ^ 2 - 1) * Real.log p)) * towerWeight p k := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog : 0 < Real.log p := Real.log_pos (by linarith)
  have hpk1 : 1 < (p : ℝ) ^ k := one_lt_pow₀ (by linarith) (by omega)
  have hpk0 : 0 < (p : ℝ) ^ k := by positivity
  have hlog_pow : (k : ℝ) * Real.log p = Real.log ((p : ℝ) ^ k) := (Real.log_pow p k).symm
  rw [hlog_pow, archLevyDensity_log hpk1, towerWeight_eq hp hk]
  have hsq : (p : ℝ) ^ k * Real.sqrt ((p : ℝ) ^ k) / (((p : ℝ) ^ k) ^ 2 - 1) =
      (1 / Real.sqrt ((p : ℝ) ^ k)) / (1 - 1 / ((p : ℝ) ^ k) ^ 2) := by
    have h1 : 0 < Real.sqrt ((p : ℝ) ^ k) := Real.sqrt_pos.mpr hpk0
    have h2 : Real.sqrt ((p : ℝ) ^ k) * Real.sqrt ((p : ℝ) ^ k) = (p : ℝ) ^ k :=
      Real.mul_self_sqrt hpk0.le
    have h3 : ((p : ℝ) ^ k) ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
    nlinarith
  rw [hsq]
  have htw : Real.log p / Real.sqrt ((p : ℝ) ^ k) / Real.log p = 1 / Real.sqrt ((p : ℝ) ^ k) := by
    field_simp [hlog.ne']
  have hden_pos : 0 < 1 - 1 / ((p : ℝ) ^ k) ^ 2 := by
    rw [sub_pos, div_lt_one (by positivity)]
    nlinarith
  have hden_lt : 1 - 1 / ((p : ℝ) ^ k) ^ 2 < 1 := by
    have : 0 < 1 / ((p : ℝ) ^ k) ^ 2 := by positivity
    linarith
  constructor
  · rw [htw, lt_div_iff₀ hden_pos]
    have h1 : 0 < 1 / Real.sqrt ((p : ℝ) ^ k) := by positivity
    nlinarith
  · have hp_le_pk : (p : ℝ) ^ 2 ≤ ((p : ℝ) ^ k) ^ 2 := by
      have : (p : ℝ) ^ 1 ≤ (p : ℝ) ^ k := pow_le_pow_right₀ (by linarith) hk
      rw [pow_one] at this
      exact pow_le_pow_left₀ hp0.le this 2
    have hden_ge : ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2 ≤ 1 - 1 / ((p : ℝ) ^ k) ^ 2 := by
      rw [show ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2 = 1 - 1 / (p : ℝ) ^ 2 by field_simp]
      have : 1 / ((p : ℝ) ^ k) ^ 2 ≤ 1 / (p : ℝ) ^ 2 :=
        one_div_le_one_div_of_le (by positivity) hp_le_pk
      linarith
    have hp2_pos : 0 < ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2 := by
      have : (1 : ℝ) < (p : ℝ) ^ 2 := by nlinarith
      positivity
    calc (1 / Real.sqrt ((p : ℝ) ^ k)) / (1 - 1 / ((p : ℝ) ^ k) ^ 2)
        ≤ (1 / Real.sqrt ((p : ℝ) ^ k)) / (((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) hp2_pos hden_ge
      _ = ((p : ℝ) ^ 2 / (((p : ℝ) ^ 2 - 1) * Real.log p)) *
            (Real.log p / Real.sqrt ((p : ℝ) ^ k)) := by
          have : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
          field_simp [hlog.ne']

/-- When `primeCofactor p a = primeCofactor p b` (`a, b ≠ 0`), `collarWeight a b` is sandwiched
between `(1 / log p) τ_p(dist(v_p a, v_p b))` and
`(p² / ((p² − 1) log p)) τ_p(dist(v_p a, v_p b))`. -/
theorem collarWeight_primeCofactor_eq_bounds {p a b : ℕ} (hp : p.Prime)
    (ha : a ≠ 0) (hb : b ≠ 0) (hcof : primeCofactor p a = primeCofactor p b) :
    towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) / Real.log p ≤
        collarWeight a b ∧
      collarWeight a b ≤
        ((p : ℝ) ^ 2 / (((p : ℝ) ^ 2 - 1) * Real.log p)) *
          towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) := by
  by_cases hab : a = b
  · subst hab
    simp [collarWeight_self, Nat.dist_self, towerWeight_zero]
  · have hk : 1 ≤ Nat.dist (a.factorization p) (b.factorization p) := by
      by_contra h0
      have hfac_p : a.factorization p = b.factorization p := by
        rcases le_or_gt (a.factorization p) (b.factorization p) with hle | hgt
        · have := Nat.dist_eq_sub_of_le hle; omega
        · have := Nat.dist_eq_sub_of_le hgt.le; rw [Nat.dist_comm] at h0; omega
      have ha_eq := primeCofactor_mul_pow p a
      have hb_eq := primeCofactor_mul_pow p b
      rw [hcof, hfac_p, hb_eq] at ha_eq
      exact hab ha_eq.symm
    have hlog_dist : |Real.log (b : ℝ) - Real.log (a : ℝ)| =
        (Nat.dist (a.factorization p) (b.factorization p) : ℝ) * Real.log p := by
      have ha_eq := (primeCofactor_mul_pow p a).symm
      have hb_eq := (primeCofactor_mul_pow p b).symm
      have hm0 : (0 : ℝ) < primeCofactor p a := by
        exact_mod_cast Nat.pos_of_ne_zero (primeCofactor_ne_zero ha)
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hlog_a : Real.log (a : ℝ) =
          Real.log (primeCofactor p a) + (a.factorization p : ℝ) * Real.log p := by
        conv_lhs => rw [ha_eq]
        push_cast
        rw [Real.log_mul hm0.ne' (pow_pos hp0 _).ne', Real.log_pow]
      have hlog_b : Real.log (b : ℝ) =
          Real.log (primeCofactor p a) + (b.factorization p : ℝ) * Real.log p := by
        conv_lhs => rw [hb_eq, ← hcof]
        push_cast
        rw [Real.log_mul hm0.ne' (pow_pos hp0 _).ne', Real.log_pow]
      rw [hlog_b, hlog_a, add_sub_add_left_eq_sub, ← sub_mul, abs_mul,
        abs_of_nonneg (Real.log_natCast_nonneg p)]
      congr 1
      rcases le_or_gt (a.factorization p) (b.factorization p) with hle | hgt
      · rw [Nat.dist_eq_sub_of_le hle, Nat.cast_sub hle, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hle))]
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hgt.le, Nat.cast_sub hgt.le,
          abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hgt.le))]
    have hcw : collarWeight a b =
        archLevyDensity ((Nat.dist (a.factorization p) (b.factorization p) : ℝ) * Real.log p) := by
      unfold collarWeight
      rw [if_neg (by tauto), hlog_dist]
    rw [hcw]
    have hbds := archLevyDensity_mul_log_prime_bounds hp hk
    exact ⟨hbds.1.le, hbds.2⟩

/-- The off-diagonal archimedean collar quadratic form on a finite set `S`:
`collarFormOn S c = ∑_{a, b ∈ S} c(a) c(b) collarWeight a b`. -/
def collarFormOn (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ S, c a * c b * collarWeight a b

/-- The `p`-slice of the intra-tower collar form on `S`. -/
def intraTowerCollarSliceForm (p : ℕ) (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ S,
    if primeCofactor p a = primeCofactor p b then c a * c b * collarWeight a b else 0

/-- The total intra-tower collar form across a finite prime set `P`. -/
def intraTowerCollarForm (P S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ p ∈ P, intraTowerCollarSliceForm p S c

/-- The cross-tower collar form on `S`: pairs `(a, b)` that differ in at least two prime
coordinates (`∀ p ∈ P, primeCofactor p a ≠ primeCofactor p b`), where `heckeIncidence a b = 0`. -/
def crossTowerCollarForm (P S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ S,
    if ∀ p ∈ P, primeCofactor p a ≠ primeCofactor p b then c a * c b * collarWeight a b else 0

/-- **Exact decomposition of the collar form into intra-tower and cross-tower parts.** On any
finite set `S` of positive integers, `collarFormOn S c` is the sum of `intraTowerCollarForm P S c`
and `crossTowerCollarForm P S c`. -/
theorem collarFormOn_eq_intra_add_cross {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ a ∈ S, a ≠ 0) (c : ℕ → ℝ) :
    collarFormOn S c = intraTowerCollarForm P S c + crossTowerCollarForm P S c := by
  unfold collarFormOn intraTowerCollarForm intraTowerCollarSliceForm crossTowerCollarForm
  rw [Finset.sum_comm (s := P)]
  have hinner : ∀ a ∈ S,
      (∑ p ∈ P, ∑ b ∈ S,
        if primeCofactor p a = primeCofactor p b then c a * c b * collarWeight a b else 0) =
      ∑ b ∈ S, ∑ p ∈ P,
        if primeCofactor p a = primeCofactor p b then c a * c b * collarWeight a b else 0 :=
    fun a _ => Finset.sum_comm
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b hb => ?_
  by_cases hab : a = b
  · subst hab
    simp [collarWeight_self]
  · by_cases hex : ∃ p ∈ P, primeCofactor p a = primeCofactor p b
    · rcases hex with ⟨p₀, hp₀P, hp₀eq⟩
      rw [if_neg (by push Not; exact ⟨p₀, hp₀P, hp₀eq⟩), add_zero]
      rw [Finset.sum_eq_single p₀]
      · rw [if_pos hp₀eq]
      · intro q hqP hqp₀
        rw [if_neg]
        intro hqeq
        exact hab (eq_of_primeCofactor_eq_of_ne (hP p₀ hp₀P) (hP q hqP) hqp₀.symm
          (hS a ha) (hS b hb) hp₀eq hqeq)
      · intro hp₀_not; exact absurd hp₀P hp₀_not
    · have hall : ∀ p ∈ P, primeCofactor p a ≠ primeCofactor p b := by
        simpa using hex
      rw [if_pos hall, Finset.sum_eq_zero (fun p hp => by rw [if_neg (hall p hp)]), zero_add]

/-- Every pair `(a, b)` contributing to `crossTowerCollarForm P S c` on a `P`-smooth set `S` has
vanishing prime Hecke incidence (`heckeIncidence a b = 0`). -/
theorem heckeIncidence_eq_zero_of_crossTower {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (haP : a.primeFactors ⊆ P) (hbP : b.primeFactors ⊆ P)
    (hcross : ∀ p ∈ P, primeCofactor p a ≠ primeCofactor p b) :
    heckeIncidence a b = 0 := by
  rw [heckeIncidence_eq_sum_primes_of_primeFactors_subset hP ha hb haP hbP]
  exact Finset.sum_eq_zero fun p hp => by rw [if_neg (hcross p hp)]

/-- **Schur bound on a single prime slice of the intra-tower collar.** For any prime `p` and any
finite set `S` of positive integers,
`|intraTowerCollarSliceForm p S c| ≤ (p² / ((p² − 1) log p)) E_p ∑_{a ∈ S} c(a)²`. -/
theorem abs_intraTowerCollarSliceForm_le {p : ℕ} (hp : p.Prime) {S : Finset ℕ}
    (hS : ∀ a ∈ S, a ≠ 0) (c : ℕ → ℝ) :
    |intraTowerCollarSliceForm p S c| ≤
      ((p : ℝ) ^ 2 / (((p : ℝ) ^ 2 - 1) * Real.log p)) * eulerEnvelope p * ∑ a ∈ S, c a ^ 2 := by
  set κ := (p : ℝ) ^ 2 / (((p : ℝ) ^ 2 - 1) * Real.log p)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog : 0 < Real.log p := Real.log_pos (by linarith)
  have hκ0 : 0 ≤ κ := by
    simp only [κ]
    have : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  have hterm : ∀ a ∈ S, ∀ b ∈ S,
      |if primeCofactor p a = primeCofactor p b then c a * c b * collarWeight a b else 0| ≤
        κ * ((c a ^ 2 / 2 + c b ^ 2 / 2) *
          (if primeCofactor p a = primeCofactor p b then
            towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) else 0)) := by
    intro a ha b hb
    split_ifs with hcof
    · rw [abs_mul, abs_of_nonneg (collarWeight_nonneg a b), abs_mul]
      have hab : |c a| * |c b| ≤ c a ^ 2 / 2 + c b ^ 2 / 2 := by
        nlinarith [sq_nonneg (|c a| - |c b|), sq_abs (c a), sq_abs (c b)]
      have hcw := (collarWeight_primeCofactor_eq_bounds hp (hS a ha) (hS b hb) hcof).2
      calc |c a| * |c b| * collarWeight a b
          ≤ (c a ^ 2 / 2 + c b ^ 2 / 2) * (κ *
              towerWeight p (Nat.dist (a.factorization p) (b.factorization p))) :=
            mul_le_mul hab hcw (collarWeight_nonneg a b) (by positivity)
        _ = κ * ((c a ^ 2 / 2 + c b ^ 2 / 2) *
              towerWeight p (Nat.dist (a.factorization p) (b.factorization p))) := by ring
    · simp
  have hsym : ∑ a ∈ S, ∑ b ∈ S,
      (c a ^ 2 / 2 + c b ^ 2 / 2) *
        (if primeCofactor p a = primeCofactor p b then
          towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) else 0) =
      ∑ a ∈ S, c a ^ 2 * ∑ b ∈ S,
        (if primeCofactor p a = primeCofactor p b then
          towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) else 0) := by
    simp only [add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun a b => c b ^ 2 / 2 *
      if primeCofactor p a = primeCofactor p b then
        towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) else 0)]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Nat.dist_comm (b.factorization p) (a.factorization p)]
    by_cases h : primeCofactor p a = primeCofactor p b
    · rw [if_pos h, if_pos h.symm]; ring
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  calc |intraTowerCollarSliceForm p S c|
      ≤ ∑ a ∈ S, ∑ b ∈ S,
          |if primeCofactor p a = primeCofactor p b then c a * c b * collarWeight a b else 0| := by
        unfold intraTowerCollarSliceForm
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ =>
          Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a ∈ S, ∑ b ∈ S, κ * ((c a ^ 2 / 2 + c b ^ 2 / 2) *
          (if primeCofactor p a = primeCofactor p b then
            towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) else 0)) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hterm a ha b hb
    _ = κ * ∑ a ∈ S, ∑ b ∈ S, (c a ^ 2 / 2 + c b ^ 2 / 2) *
          (if primeCofactor p a = primeCofactor p b then
            towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
    _ = κ * ∑ a ∈ S, c a ^ 2 * ∑ b ∈ S,
          (if primeCofactor p a = primeCofactor p b then
            towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) else 0) := by
        rw [hsym]
    _ ≤ κ * ∑ a ∈ S, c a ^ 2 * eulerEnvelope p :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left
            (sum_primeSlice_towerWeight_le hp ha) (sq_nonneg _)) hκ0
    _ = κ * eulerEnvelope p * ∑ a ∈ S, c a ^ 2 := by rw [← Finset.sum_mul]; ring

/-- **The intra-tower collar coupling is bounded against the Euler envelopes.** For any finite set
`P` of primes and any finite set `S` of positive integers,
`|intraTowerCollarForm P S c| ≤ (∑_{p ∈ P} (p² / ((p² − 1) log p)) E_p) ∑_{a ∈ S} c(a)²`. -/
theorem abs_intraTowerCollarForm_le {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ a ∈ S, a ≠ 0) (c : ℕ → ℝ) :
    |intraTowerCollarForm P S c| ≤
      (∑ p ∈ P, ((p : ℝ) ^ 2 / (((p : ℝ) ^ 2 - 1) * Real.log p)) * eulerEnvelope p) *
        ∑ a ∈ S, c a ^ 2 := by
  unfold intraTowerCollarForm
  rw [Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun p hp => abs_intraTowerCollarSliceForm_le (hP p hp) hS c)

/-- On nonnegative coefficients `c ≥ 0`, each intra-tower collar slice is sandwiched between
`(1 / log p) primeSliceForm p S c` and `(p² / ((p² − 1) log p)) primeSliceForm p S c`. -/
theorem intraTowerCollarSliceForm_bounds_of_nonneg {p : ℕ} (hp : p.Prime) {S : Finset ℕ}
    (hS : ∀ a ∈ S, a ≠ 0) {c : ℕ → ℝ} (hc : ∀ a ∈ S, 0 ≤ c a) :
    primeSliceForm p S c / Real.log p ≤ intraTowerCollarSliceForm p S c ∧
      intraTowerCollarSliceForm p S c ≤
        ((p : ℝ) ^ 2 / (((p : ℝ) ^ 2 - 1) * Real.log p)) * primeSliceForm p S c := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog : 0 < Real.log p := Real.log_pos (by linarith)
  unfold primeSliceForm intraTowerCollarSliceForm
  rw [Finset.sum_div, Finset.mul_sum]
  constructor
  · refine Finset.sum_le_sum fun a ha => ?_
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun b hb => ?_
    split_ifs with hcof
    · rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left
        (collarWeight_primeCofactor_eq_bounds hp (hS a ha) (hS b hb) hcof).1
        (mul_nonneg (hc a ha) (hc b hb))
    · simp
  · refine Finset.sum_le_sum fun a ha => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    split_ifs with hcof
    · have hcw := (collarWeight_primeCofactor_eq_bounds hp (hS a ha) (hS b hb) hcof).2
      exact (mul_le_mul_of_nonneg_left hcw (mul_nonneg (hc a ha) (hc b hb))).trans_eq (by ring)
    · simp

/-- **Pointwise bound on the collar weight against the polar weight `√(b/a) + √(a/b)`.** For any
`1 ≤ a < b`, because `b − a ≥ 1` and `4ab ≤ (a + b)²`,
`collarWeight a b ≤ (b / 4) (√(b/a) + √(a/b))`. -/
theorem collarWeight_le_polarWeight_mul {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    collarWeight a b ≤
      ((b : ℝ) / 4) * (Real.sqrt ((b : ℝ) / a) + Real.sqrt ((a : ℝ) / b)) := by
  rw [collarWeight_eq_of_lt ha hab]
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hba1 : (1 : ℝ) ≤ (b : ℝ) - a := by
    have : a + 1 ≤ b := hab
    have : (a : ℝ) + 1 ≤ b := by exact_mod_cast this
    linarith
  have hpol : Real.sqrt ((b : ℝ) / a) + Real.sqrt ((a : ℝ) / b) =
      ((a : ℝ) + b) / Real.sqrt ((a : ℝ) * b) := by
    have hs : 0 < Real.sqrt ((a : ℝ) * b) := Real.sqrt_pos.mpr (mul_pos ha0 hb0)
    rw [Real.sqrt_div hb0.le, Real.sqrt_div ha0.le, Real.sqrt_mul ha0.le]
    have h1 : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
    have h2 : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb0
    field_simp
    rw [Real.sq_sqrt ha0.le, Real.sq_sqrt hb0.le, add_comm]
  have hpol2 : ((b : ℝ) / 4) * (Real.sqrt ((b : ℝ) / a) + Real.sqrt ((a : ℝ) / b)) =
      ((b : ℝ) * ((a : ℝ) + b)) / (4 * Real.sqrt ((a : ℝ) * b)) := by
    rw [hpol]
    ring
  rw [hpol2]
  have hs : 0 < Real.sqrt ((a : ℝ) * b) := Real.sqrt_pos.mpr (mul_pos ha0 hb0)
  have hden_pos : 0 < (b : ℝ) ^ 2 - (a : ℝ) ^ 2 := by nlinarith
  rw [div_le_div_iff₀ hden_pos (by positivity)]
  have hsq : Real.sqrt ((a : ℝ) * b) * Real.sqrt ((a : ℝ) * b) = (a : ℝ) * b :=
    Real.mul_self_sqrt (mul_pos ha0 hb0).le
  have h4ab : 4 * ((a : ℝ) * b) ≤ ((a : ℝ) + b) ^ 2 := by
    nlinarith [sq_nonneg ((a : ℝ) - b)]
  have hdiff : (a : ℝ) + b ≤ ((b : ℝ) - a) * ((a : ℝ) + b) := by
    nlinarith
  calc (b : ℝ) * Real.sqrt ((a : ℝ) * b) * (4 * Real.sqrt ((a : ℝ) * b))
      = (b : ℝ) * (4 * ((a : ℝ) * b)) := by
        linear_combination 4 * (b : ℝ) * hsq
    _ ≤ (b : ℝ) * (((a : ℝ) + b) ^ 2) := mul_le_mul_of_nonneg_left h4ab hb0.le
    _ ≤ (b : ℝ) * ((a : ℝ) + b) * ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) := by
        have : (b : ℝ) ^ 2 - (a : ℝ) ^ 2 = ((b : ℝ) - a) * ((a : ℝ) + b) := by ring
        rw [this]
        nlinarith

/-- In the dyadically separated regime `2a ≤ b` (`a ≥ 1`), `collarWeight a b ≤ (4/3) √(a/b)`. -/
theorem collarWeight_le_of_two_mul_le {a b : ℕ} (ha : 1 ≤ a) (hab : 2 * a ≤ b) :
    collarWeight a b ≤ (4 / 3 : ℝ) * Real.sqrt ((a : ℝ) / b) := by
  have hlt : a < b := by omega
  rw [collarWeight_eq_of_lt ha hlt]
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hab' : 2 * (a : ℝ) ≤ b := by exact_mod_cast hab
  have hden : (3 / 4 : ℝ) * (b : ℝ) ^ 2 ≤ (b : ℝ) ^ 2 - (a : ℝ) ^ 2 := by nlinarith
  have hsq : (b : ℝ) * Real.sqrt ((a : ℝ) * b) = (b : ℝ) ^ 2 * Real.sqrt ((a : ℝ) / b) := by
    rw [Real.sqrt_mul ha0.le, Real.sqrt_div ha0.le]
    have hsb0 : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr hb0).ne'
    field_simp
    rw [Real.sq_sqrt hb0.le]
  rw [hsq, div_le_iff₀ (by nlinarith)]
  calc (b : ℝ) ^ 2 * Real.sqrt ((a : ℝ) / b)
      = (4 / 3 : ℝ) * Real.sqrt ((a : ℝ) / b) * ((3 / 4 : ℝ) * (b : ℝ) ^ 2) := by ring
    _ ≤ (4 / 3 : ℝ) * Real.sqrt ((a : ℝ) / b) * ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

/-- **Pointwise Lévy–Bochner identity for a disjointly supported family of bumps.** For any finite
set `S`, pairwise disjointly supported real functions `g : ℕ → ℝ → ℝ`, and coefficients `c : ℕ → ℝ`,
the squared shift difference of `F = ∑_{a ∈ S} c(a) g_a` equals the sum of the diagonal squared
shift differences minus the off-diagonal collar cross-terms. -/
theorem disjoint_family_shift_sq_eq {S : Finset ℕ} {g : ℕ → ℝ → ℝ}
    (hdisj : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ u : ℝ, g a u * g b u = 0)
    (c : ℕ → ℝ) (u x : ℝ) :
    ((∑ a ∈ S, c a * g a u) - ∑ a ∈ S, c a * g a (u + x)) ^ 2 =
      (∑ a ∈ S, c a ^ 2 * (g a u - g a (u + x)) ^ 2) -
        ∑ a ∈ S, ∑ b ∈ S.erase a, c a * c b * (g a u * g b (u + x) + g a (u + x) * g b u) := by
  have hsub : (∑ a ∈ S, c a * g a u) - ∑ a ∈ S, c a * g a (u + x) =
      ∑ a ∈ S, c a * (g a u - g a (u + x)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hsub, sq, Finset.sum_mul_sum]
  have hrow : ∀ a ∈ S,
      (∑ b ∈ S, c a * (g a u - g a (u + x)) * (c b * (g b u - g b (u + x)))) =
        c a ^ 2 * (g a u - g a (u + x)) ^ 2 -
          ∑ b ∈ S.erase a, c a * c b * (g a u * g b (u + x) + g a (u + x) * g b u) := by
    intro a ha
    rw [← Finset.add_sum_erase _ _ ha]
    have hdiag : c a * (g a u - g a (u + x)) * (c a * (g a u - g a (u + x))) =
        c a ^ 2 * (g a u - g a (u + x)) ^ 2 := by ring
    have hoff : ∀ b ∈ S.erase a,
        c a * (g a u - g a (u + x)) * (c b * (g b u - g b (u + x))) =
          -(c a * c b * (g a u * g b (u + x) + g a (u + x) * g b u)) := by
      intro b hb
      have hba : b ≠ a := (Finset.mem_erase.mp hb).1
      have hbS : b ∈ S := Finset.mem_of_mem_erase hb
      have h1 := hdisj a ha b hbS hba.symm u
      have h2 := hdisj a ha b hbS hba.symm (u + x)
      linear_combination c a * c b * h1 + c a * c b * h2
    rw [hdiag, Finset.sum_congr rfl hoff, Finset.sum_neg_distrib]
    ring
  rw [Finset.sum_congr rfl hrow, Finset.sum_sub_distrib]

/-- **The off-diagonal continuum collar coupling is universally bounded by the diagonal shift-jump
energy.** -/
theorem disjoint_lattice_collar_le_selfJump {S : Finset ℕ} {g : ℕ → ℝ → ℝ}
    (hdisj : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ u : ℝ, g a u * g b u = 0)
    (c : ℕ → ℝ) (u x : ℝ) :
    ∑ a ∈ S, ∑ b ∈ S.erase a, c a * c b * (g a u * g b (u + x) + g a (u + x) * g b u) ≤
      ∑ a ∈ S, c a ^ 2 * (g a u - g a (u + x)) ^ 2 := by
  have hid := disjoint_family_shift_sq_eq hdisj c u x
  have hsq : 0 ≤ ((∑ a ∈ S, c a * g a u) - ∑ a ∈ S, c a * g a (u + x)) ^ 2 := sq_nonneg _
  linarith

/-! ## §4. Positivity decision for the finite-Euler-product form on lattice tests -/

/-- The finite-Euler-product quadratic form on a finite set `S` at diagonal budget `κ`:
`finiteEulerLatticeForm S κ c = κ ∑_{a ∈ S} c(a)² − heckeFormOn S c`. -/
def finiteEulerLatticeForm (S : Finset ℕ) (κ : ℝ) (c : ℕ → ℝ) : ℝ :=
  κ * (∑ a ∈ S, c a ^ 2) - heckeFormOn S c

/-- **Sufficient condition for positivity on any `P`-smooth support.** Whenever
`∑_{p ∈ P} E_p ≤ κ`, `finiteEulerLatticeForm S κ c` is nonnegative for all `c`, with coercivity
margin `(κ − ∑_{p ∈ P} E_p) ∑_{a ∈ S} c(a)²`. -/
theorem finiteEulerLatticeForm_ge_of_sum_eulerEnvelope {P S : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hS : ∀ a ∈ S, a ≠ 0 ∧ a.primeFactors ⊆ P)
    (κ : ℝ) (c : ℕ → ℝ) :
    (κ - ∑ p ∈ P, eulerEnvelope p) * (∑ a ∈ S, c a ^ 2) ≤
      finiteEulerLatticeForm S κ c := by
  unfold finiteEulerLatticeForm
  have hle := (le_abs_self _).trans (abs_heckeFormOn_le_sum_eulerEnvelope hP hS c)
  linarith

theorem finiteEulerLatticeForm_nonneg_of_sum_eulerEnvelope_le {P S : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hS : ∀ a ∈ S, a ≠ 0 ∧ a.primeFactors ⊆ P)
    {κ : ℝ} (hκ : ∑ p ∈ P, eulerEnvelope p ≤ κ) (c : ℕ → ℝ) :
    0 ≤ finiteEulerLatticeForm S κ c := by
  refine le_trans ?_ (finiteEulerLatticeForm_ge_of_sum_eulerEnvelope hP hS κ c)
  exact mul_nonneg (sub_nonneg.mpr hκ) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem finiteEulerLatticeForm_pos_of_sum_eulerEnvelope_lt {P S : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hS : ∀ a ∈ S, a ≠ 0 ∧ a.primeFactors ⊆ P)
    {κ : ℝ} (hκ : ∑ p ∈ P, eulerEnvelope p < κ) {c : ℕ → ℝ} (hc : 0 < ∑ a ∈ S, c a ^ 2) :
    0 < finiteEulerLatticeForm S κ c := by
  refine lt_of_lt_of_le ?_ (finiteEulerLatticeForm_ge_of_sum_eulerEnvelope hP hS κ c)
  exact mul_pos (sub_pos.mpr hκ) hc

/-- **Sharpness of the `E_p + E_q` positivity threshold on `{p, q}`-boxes.** For any distinct
primes `p ≠ q`, `κ ≥ E_p + E_q` is both necessary and sufficient for the box form
`κ ∑_{x ∈ range M ×ˢ range N} c(x)² − heckeForm p q M N c` to be nonnegative for all box sizes
`M, N` and all coefficient vectors `c`: if `κ < E_p + E_q`, the constant resonant train `c ≡ 1`
makes the form strictly negative for sufficiently large `M, N ≥ 1`. -/
theorem exists_finiteEulerLatticeForm_box_neg_of_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {κ : ℝ} (hκ : κ < eulerEnvelope p + eulerEnvelope q) :
    ∃ M N : ℕ, 1 ≤ M ∧ 1 ≤ N ∧
      κ * (∑ _x ∈ range M ×ˢ range N, (1 : ℝ) ^ 2) - heckeForm p q M N (fun _ => 1) < 0 := by
  obtain ⟨M, N, hM1, hN1, hgt⟩ := exists_heckeForm_box_one_gt_of_lt_add_eulerEnvelope hp hq hpq hκ
  refine ⟨M, N, hM1, hN1, ?_⟩
  have hsum : (∑ _x ∈ range M ×ˢ range N, (1 : ℝ) ^ 2) = (M : ℝ) * N := by
    simp [Finset.sum_const, Finset.card_product, Finset.card_range, nsmul_eq_mul]
  rw [hsum]
  linarith

/-- **Exact characterization of universal box positivity for two prime towers.** For distinct
primes `p ≠ q`, the finite-Euler-product form on `{p, q}`-boxes is positive semidefinite across all
box dimensions `M, N` iff `E_p + E_q ≤ κ`. -/
theorem box_finiteEulerForm_nonneg_forall_iff {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (κ : ℝ) :
    (∀ M N : ℕ, ∀ c : ℕ × ℕ → ℝ,
      0 ≤ κ * (∑ x ∈ range M ×ˢ range N, c x ^ 2) - heckeForm p q M N c) ↔
      eulerEnvelope p + eulerEnvelope q ≤ κ := by
  constructor
  · intro hall
    by_contra hlt
    push Not at hlt
    obtain ⟨M, N, _, _, hneg⟩ := exists_finiteEulerLatticeForm_box_neg_of_lt hp hq hpq hlt
    linarith [hall M N (fun _ => 1)]
  · intro hκ M N c
    have hle := (le_abs_self _).trans (abs_heckeForm_box_le hp hq hpq M N c)
    have hE : 2 * (Real.log p / (Real.sqrt p - 1)) + 2 * (Real.log q / (Real.sqrt q - 1)) =
        eulerEnvelope p + eulerEnvelope q := by
      unfold eulerEnvelope; ring
    rw [hE] at hle
    have hsum : 0 ≤ ∑ x ∈ range M ×ˢ range N, c x ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hκ hsum]

/-- The collar-coupled finite-Euler-product quadratic form on `S`:
`collarCoupledEulerLatticeForm S κ c = κ ∑_{a ∈ S} c(a)² − heckeFormOn S c − collarFormOn S c`. -/
def collarCoupledEulerLatticeForm (S : Finset ℕ) (κ : ℝ) (c : ℕ → ℝ) : ℝ :=
  κ * (∑ a ∈ S, c a ^ 2) - heckeFormOn S c - collarFormOn S c

/-- **Coercivity of the collar-coupled finite-Euler-product form.** On any finite set `S` of
positive `P`-smooth integers, if `|crossTowerCollarForm P S c| ≤ C_cross ∑_{a ∈ S} c(a)²`, then
`collarCoupledEulerLatticeForm S κ c` is bounded below by
`(κ − ∑_{p ∈ P} (1 + p² / ((p² − 1) log p)) E_p − C_cross) ∑_{a ∈ S} c(a)²`. -/
theorem collarCoupledEulerLatticeForm_ge {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ a ∈ S, a ≠ 0 ∧ a.primeFactors ⊆ P) (κ C_cross : ℝ) (c : ℕ → ℝ)
    (hcross : |crossTowerCollarForm P S c| ≤ C_cross * ∑ a ∈ S, c a ^ 2) :
    (κ - (∑ p ∈ P, (1 + (p : ℝ) ^ 2 / (((p : ℝ) ^ 2 - 1) * Real.log p)) * eulerEnvelope p) -
        C_cross) * (∑ a ∈ S, c a ^ 2) ≤
      collarCoupledEulerLatticeForm S κ c := by
  unfold collarCoupledEulerLatticeForm
  rw [collarFormOn_eq_intra_add_cross hP (fun a ha => (hS a ha).1) c]
  have h1 := (le_abs_self _).trans (abs_heckeFormOn_le_sum_eulerEnvelope hP hS c)
  have h2 := (le_abs_self _).trans (abs_intraTowerCollarForm_le hP (fun a ha => (hS a ha).1) c)
  have h3 := (le_abs_self _).trans hcross
  have hsum : ∑ p ∈ P, (1 + (p : ℝ) ^ 2 / (((p : ℝ) ^ 2 - 1) * Real.log p)) * eulerEnvelope p =
      (∑ p ∈ P, eulerEnvelope p) +
        ∑ p ∈ P, ((p : ℝ) ^ 2 / (((p : ℝ) ^ 2 - 1) * Real.log p)) * eulerEnvelope p := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsum]
  linarith

theorem collarCoupledEulerLatticeForm_nonneg {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ a ∈ S, a ≠ 0 ∧ a.primeFactors ⊆ P) {κ C_cross : ℝ} {c : ℕ → ℝ}
    (hcross : |crossTowerCollarForm P S c| ≤ C_cross * ∑ a ∈ S, c a ^ 2)
    (hκ : (∑ p ∈ P, (1 + (p : ℝ) ^ 2 / (((p : ℝ) ^ 2 - 1) * Real.log p)) * eulerEnvelope p) +
      C_cross ≤ κ) :
    0 ≤ collarCoupledEulerLatticeForm S κ c := by
  refine le_trans ?_ (collarCoupledEulerLatticeForm_ge hP hS κ C_cross c hcross)
  exact mul_nonneg (by linarith) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The discrete polar pairing on a lattice support `S`:
`latticePolarForm S c = ∑_{a, b ∈ S} c(a) c(b) (√(b/a) + √(a/b)) = 2 (∑_{a ∈ S} c(a) a^{−1/2}) (∑_{b ∈ S} c(b) b^{1/2})`. -/
def latticePolarForm (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ S, c a * c b * (Real.sqrt ((b : ℝ) / a) + Real.sqrt ((a : ℝ) / b))

/-- On nonnegative coefficients `c ≥ 0` supported on `S ⊂ [1, B_max]`, the polar form pays the
entire off-diagonal collar (and in particular the cross-tower collar):
`collarFormOn S c ≤ (B_max / 4) latticePolarForm S c`. -/
theorem collarFormOn_le_latticePolarForm {S : Finset ℕ} {B_max : ℕ}
    (hS : ∀ a ∈ S, 1 ≤ a ∧ a ≤ B_max) {c : ℕ → ℝ} (hc : ∀ a ∈ S, 0 ≤ c a) :
    collarFormOn S c ≤ ((B_max : ℝ) / 4) * latticePolarForm S c := by
  unfold collarFormOn latticePolarForm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a ha => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b hb => ?_
  have hca := hc a ha
  have hcb := hc b hb
  have hcab : 0 ≤ c a * c b := mul_nonneg hca hcb
  have hcw : collarWeight a b ≤
      ((B_max : ℝ) / 4) * (Real.sqrt ((b : ℝ) / a) + Real.sqrt ((a : ℝ) / b)) := by
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · calc collarWeight a b
          ≤ ((b : ℝ) / 4) * (Real.sqrt ((b : ℝ) / a) + Real.sqrt ((a : ℝ) / b)) :=
            collarWeight_le_polarWeight_mul (hS a ha).1 hlt
        _ ≤ ((B_max : ℝ) / 4) * (Real.sqrt ((b : ℝ) / a) + Real.sqrt ((a : ℝ) / b)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have : (b : ℝ) ≤ B_max := by exact_mod_cast (hS b hb).2
            linarith
    · rw [collarWeight_self]
      positivity
    · rw [collarWeight_comm, add_comm (Real.sqrt ((b : ℝ) / a))]
      calc collarWeight b a
          ≤ ((a : ℝ) / 4) * (Real.sqrt ((a : ℝ) / b) + Real.sqrt ((b : ℝ) / a)) :=
            collarWeight_le_polarWeight_mul (hS b hb).1 hgt
        _ ≤ ((B_max : ℝ) / 4) * (Real.sqrt ((a : ℝ) / b) + Real.sqrt ((b : ℝ) / a)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have : (a : ℝ) ≤ B_max := by exact_mod_cast (hS a ha).2
            linarith
  exact (mul_le_mul_of_nonneg_left hcw hcab).trans_eq (by ring)

/-- **Pole-compensated positivity of the collar-coupled finite-Euler-product form on effective
lattice cycles.** When the polar pairing is included with weight `λ_pole ≥ B_max / 4`, it pays the
entire collar on nonnegative coefficients `c ≥ 0`, so `κ ≥ ∑_{p ∈ P} E_p` suffices for positivity:
`0 ≤ collarCoupledEulerLatticeForm S κ c + λ_pole * latticePolarForm S c`. -/
theorem poleCompensatedCollarLatticeForm_nonneg {P S : Finset ℕ} {B_max : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hS : ∀ a ∈ S, (1 ≤ a ∧ a ≤ B_max) ∧ a.primeFactors ⊆ P)
    {κ lam_pole : ℝ} (hκ : ∑ p ∈ P, eulerEnvelope p ≤ κ)
    (hlam : (B_max : ℝ) / 4 ≤ lam_pole) {c : ℕ → ℝ} (hc : ∀ a ∈ S, 0 ≤ c a) :
    0 ≤ collarCoupledEulerLatticeForm S κ c + lam_pole * latticePolarForm S c := by
  have hS_ne : ∀ a ∈ S, a ≠ 0 ∧ a.primeFactors ⊆ P := fun a ha => by
    have h1 := (hS a ha).1.1
    exact ⟨by omega, (hS a ha).2⟩
  have hfe := finiteEulerLatticeForm_nonneg_of_sum_eulerEnvelope_le hP hS_ne hκ c
  have hcol := collarFormOn_le_latticePolarForm (fun a ha => (hS a ha).1) hc
  have hpol_nonneg : 0 ≤ latticePolarForm S c :=
    Finset.sum_nonneg fun a ha => Finset.sum_nonneg fun b hb =>
      mul_nonneg (mul_nonneg (hc a ha) (hc b hb)) (by positivity)
  have hlam_col : collarFormOn S c ≤ lam_pole * latticePolarForm S c :=
    hcol.trans (mul_le_mul_of_nonneg_right hlam hpol_nonneg)
  unfold collarCoupledEulerLatticeForm finiteEulerLatticeForm at *
  linarith

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
