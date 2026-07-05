/-
Route B′ seed-gap arithmetic — (SEED-GAP) typed exactly (heir card; corrects
doc 84 §9's sketch identity).

The heir's candidate density seed is the rough inverse product
Π_z = Π_{z<p≤N} (1 − p^{-s})^{-1}, the Dirichlet series over z-rough numbers
(all prime factors > z).  Doc 84 §9 typed the seed-carrier relation as
"F_N·M_z = Π_z − D_z with E|D_z|² = O(1) (the n > N rough tail)".  Typing the
defect on the divisor-window surface shows that identity is FALSE as written:
D_z also carries the inner Legendre-truncation error (m ≤ N, non-rough) and
the boundary band (N < m ≤ Nz) — and the boundary band is exactly the
loglog-critical object of the Route B refutation (doc 85 §3′).  What is true,
and proved here, is the exact decomposition:

* `rough_window_filter_eq_one` / `rough_window_coeff_eq_lam_one` — on every
  z-rough element n ≤ N the divisor window collapses to {1}, so the carrier
  coefficient is λ₁ for ANY weights supported on [1, z] (sharp μ and BV
  alike).  With the normalization λ₁ = 1 the carrier and the seed agree
  EXACTLY on the whole rough support up to N.
* `seedGap_rough_component_secondMoment_zero` — the packet-observable face:
  over any finite prime support in (z, N], the interval L² distance between
  the carrier packet and the seed packet is ZERO on every vertical interval
  (consumes the LogIndependenceCompare union-padding surface).
* `singleton_window_filter_eq` / `singleton_window_coeff_eq_lam` /
  `seedGap_boundary_coeff` — on a singleton-window boundary element p·d the
  divisor window is exactly {d}: the carrier coefficient is λ_d, the seed
  coefficient is 0 (p·d is not rough), so the GAP coefficient is λ_d on the
  nose — the cancellation-free sub-family of the V_bd ≳ loglog N bound.
* `dpoly_shift_norm` / `boundary_gap_packet_secondMoment_pos_iff` — the gap
  packet at fixed d has strictly positive L² mass on EVERY nonempty vertical
  interval iff λ_d ≠ 0: the common factor d contributes only a unimodular
  phase d^{-it}, so the boundary packet inherits the prime-packet positivity
  criterion (Hurwitz-backed).  No mollifier design cancels the boundary band
  on any window — machine-checked at the observable level.

Consequence for the heir card: the O(1)-L² asset is dead; the seed matches
the carrier exactly on rough support ≤ N, and the ENTIRE gap is the
windowed-divisor defect, whose boundary part is loglog-critical with
coefficient λ_d exactly.  A seed-transfer for the heir must be density-level
on the matched rough component, not an L² perturbation.
-/
import GaloisForLFunctions.RHTower.RouteBSupport
import GaloisForLFunctions.RHTower.LogIndependence
import GaloisForLFunctions.RHTower.LogIndependenceCompare

namespace RHTower

open Complex

/-- A z-smooth divisor `2 ≤ d ≤ z` certifies non-roughness of any multiple:
its least prime factor is a prime ≤ z dividing the multiple. -/
theorem not_rough_of_smooth_divisor {z d n : ℕ} (hd2 : 2 ≤ d) (hdz : d ≤ z)
    (hdn : d ∣ n) : ¬ (∀ p, p.Prime → p ∣ n → z < p) := by
  intro hrough
  have hp : d.minFac.Prime := Nat.minFac_prime (by omega)
  have hple : d.minFac ≤ d := Nat.minFac_le (by omega)
  have hpn : d.minFac ∣ n := dvd_trans (Nat.minFac_dvd d) hdn
  have := hrough d.minFac hp hpn
  omega

/-- On a z-rough element `n ≤ N` the divisor window collapses to `{1}`:
every divisor `1 < e ≤ z` would carry a prime ≤ z into `n`. -/
theorem rough_window_filter_eq_one {N z n : ℕ} (hn : 0 < n) (hnN : n ≤ N)
    (hz : 1 ≤ z) (hrough : ∀ p, p.Prime → p ∣ n → z < p) :
    n.divisors.filter (fun e => e ≤ z ∧ n ≤ N * e) = {1} := by
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  · rw [Finset.mem_filter]
    exact ⟨Nat.one_mem_divisors.mpr (by omega), hz, by omega⟩
  · intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨hmem, hez, _⟩ := he
    have hedvd : e ∣ n := (Nat.mem_divisors.mp hmem).1
    have hepos : 0 < e := Nat.pos_of_mem_divisors hmem
    by_contra hne
    exact not_rough_of_smooth_divisor (by omega) hez hedvd hrough

/-- **Seed–carrier agreement on the rough support.**  For every z-rough
`n ≤ N` the carrier's window coefficient is `lam 1` — for ANY mollifier
weights supported on `[1, z]`. -/
theorem rough_window_coeff_eq_lam_one (lam : ℕ → ℝ) {N z n : ℕ} (hn : 0 < n)
    (hnN : n ≤ N) (hz : 1 ≤ z) (hrough : ∀ p, p.Prime → p ∣ n → z < p) :
    ∑ e ∈ n.divisors.filter (fun e => e ≤ z ∧ n ≤ N * e), lam e = lam 1 := by
  rw [rough_window_filter_eq_one hn hnN hz hrough, Finset.sum_singleton]

/-- Primes in `(z, N]` are z-rough: their carrier coefficient is `lam 1`. -/
theorem prime_window_coeff_eq_lam_one (lam : ℕ → ℝ) {N z p : ℕ} (hp : p.Prime)
    (hpz : z < p) (hpN : p ≤ N) (hz : 1 ≤ z) :
    ∑ e ∈ p.divisors.filter (fun e => e ≤ z ∧ p ≤ N * e), lam e = lam 1 := by
  refine rough_window_coeff_eq_lam_one lam hp.pos hpN hz ?_
  intro q hq hqp
  have : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
  omega

/-- The boundary singleton window: at `p·d` with `p` prime above `y` and
`N < p·minFac d`, the divisor window is exactly `{d}`. -/
theorem singleton_window_filter_eq {N y p d : ℕ} (hp : p.Prime) (hpy : y < p)
    (hd : 0 < d) (hdy : d ≤ y) (hpN : p ≤ N) (hbig : N < p * d.minFac) :
    (p * d).divisors.filter (fun e => e ≤ y ∧ p * d ≤ N * e) = {d} := by
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  · rw [Finset.mem_filter]
    exact ⟨Nat.mem_divisors.mpr ⟨dvd_mul_left d p, (Nat.mul_pos hp.pos hd).ne'⟩,
      hdy, Nat.mul_le_mul_right d hpN⟩
  · intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨hmem, hey, hwin⟩ := he
    exact singleton_window_coeff hp hpy hd hbig (Nat.mem_divisors.mp hmem).1 hey hwin

/-- **The boundary carrier coefficient is exactly `lam d`.** -/
theorem singleton_window_coeff_eq_lam (lam : ℕ → ℝ) {N y p d : ℕ}
    (hp : p.Prime) (hpy : y < p) (hd : 0 < d) (hdy : d ≤ y) (hpN : p ≤ N)
    (hbig : N < p * d.minFac) :
    ∑ e ∈ (p * d).divisors.filter (fun e => e ≤ y ∧ p * d ≤ N * e), lam e
      = lam d := by
  rw [singleton_window_filter_eq hp hpy hd hdy hpN hbig, Finset.sum_singleton]

/-- **The seed-gap boundary coefficient, packaged.**  On a singleton-window
boundary element `p·d` (`2 ≤ d`) the carrier coefficient is `lam d` AND the
element is not y-rough (the seed coefficient is 0): the gap coefficient is
`lam d` on the nose, for every admissible weight system. -/
theorem seedGap_boundary_coeff (lam : ℕ → ℝ) {N y p d : ℕ} (hp : p.Prime)
    (hpy : y < p) (hd2 : 2 ≤ d) (hdy : d ≤ y) (hpN : p ≤ N)
    (hbig : N < p * d.minFac) :
    (∑ e ∈ (p * d).divisors.filter (fun e => e ≤ y ∧ p * d ≤ N * e), lam e
        = lam d)
      ∧ ¬ (∀ q, q.Prime → q ∣ p * d → y < q) :=
  ⟨singleton_window_coeff_eq_lam lam hp hpy (by omega) hdy hpN hbig,
   not_rough_of_smooth_divisor hd2 hdy (dvd_mul_left d p)⟩

end RHTower

namespace RHTower

open Complex

/-- Frequency-shift modulus identity: a packet supported on `{p·d : p ∈ P}`
has the same pointwise modulus as the prime packet with shifted coefficients —
the common factor `d` contributes only the unimodular phase `d^{-it}`. -/
theorem dpoly_shift_norm (a : ℕ → ℝ) {P : Finset ℕ} (hP : ∀ p ∈ P, 0 < p)
    {d : ℕ} (hd : 0 < d) (t : ℝ) :
    ‖dpoly a (P.image (fun p => p * d)) t‖
      = ‖dpoly (fun p => a (p * d)) P t‖ := by
  have hinj : Set.InjOn (fun p => p * d) ↑P := fun x _ y _ hxy =>
    Nat.eq_of_mul_eq_mul_right hd hxy
  have hterm : ∀ p ∈ P, cterm a t (p * d)
      = Complex.exp (-(t : ℂ) * Complex.I * (Real.log d : ℂ))
        * cterm (fun q => a (q * d)) t p := by
    intro p hpP
    unfold cterm
    have hlog : Real.log ((p * d : ℕ) : ℝ) = Real.log p + Real.log d := by
      push_cast
      exact Real.log_mul (by exact_mod_cast (hP p hpP).ne') (by exact_mod_cast hd.ne')
    rw [hlog, Complex.ofReal_add, mul_add, Complex.exp_add]
    ring
  have hre : (-(t : ℂ) * Complex.I * (Real.log d : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hnorm : ‖Complex.exp (-(t : ℂ) * Complex.I * (Real.log d : ℂ))‖ = 1 := by
    rw [Complex.norm_exp, hre, Real.exp_zero]
  have hsum : dpoly a (P.image (fun p => p * d)) t
      = Complex.exp (-(t : ℂ) * Complex.I * (Real.log d : ℂ))
        * dpoly (fun q => a (q * d)) P t := by
    unfold dpoly
    rw [Finset.sum_image hinj, Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  rw [hsum, norm_mul, hnorm, one_mul]

/-- **The rough component of the seed gap has ZERO interval energy.**  Over
any finite prime support in `(z, N]` the carrier packet (divisor-window
coefficients) and the seed packet (coefficient 1) are at interval L² distance
zero on every vertical interval, for any weights with `lam 1 = 1`. -/
theorem seedGap_rough_component_secondMoment_zero (lam : ℕ → ℝ)
    (hlam1 : lam 1 = 1) {N z : ℕ} (hz : 1 ≤ z) {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hPz : ∀ p ∈ P, z < p) (hPN : ∀ p ∈ P, p ≤ N)
    {A B : ℝ} (hAB : A < B) :
    (∫ x in A..B,
      ‖dpoly (fun n => ∑ e ∈ n.divisors.filter (fun e => e ≤ z ∧ n ≤ N * e),
            lam e) P x
        - dpoly (fun _ => (1 : ℝ)) P x‖ ^ 2) = 0 := by
  rw [dpoly_prime_finset_secondMoment_sub_eq_zero_iff_coeff_eq_on_union
    P P hP hP hAB]
  intro p hpmem
  rw [Finset.union_self] at hpmem
  simp only [hpmem, if_pos]
  rw [prime_window_coeff_eq_lam_one lam (hP p hpmem) (hPz p hpmem)
    (hPN p hpmem) hz, hlam1]

/-- **The boundary gap packet is cancellation-free at the observable level.**
At fixed `d`, the seed-gap packet over the boundary elements `{p·d : p ∈ P}`
has strictly positive L² mass on EVERY nonempty vertical interval iff
`lam d ≠ 0`.  The Lean face of the windowed-divisor criticality mechanism
(doc 85 §3′): no choice of mollifier weights cancels the boundary band on any
window. -/
theorem boundary_gap_packet_secondMoment_pos_iff (lam : ℕ → ℝ) {d : ℕ}
    (hd : 0 < d) {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hPne : P.Nonempty)
    {A B : ℝ} (hAB : A < B) :
    (0 < ∫ x in A..B,
        ‖dpoly (fun _ => lam d) (P.image (fun p => p * d)) x‖ ^ 2)
      ↔ lam d ≠ 0 := by
  have hshift : ∀ x : ℝ,
      ‖dpoly (fun _ => lam d) (P.image (fun p => p * d)) x‖
        = ‖dpoly (fun _ => lam d) P x‖ := fun x =>
    dpoly_shift_norm (fun _ => lam d) (fun p hpP => (hP p hpP).pos) hd x
  have hint : (∫ x in A..B,
        ‖dpoly (fun _ => lam d) (P.image (fun p => p * d)) x‖ ^ 2)
      = ∫ x in A..B, ‖dpoly (fun _ => lam d) P x‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x _
    exact congrArg (fun r : ℝ => r ^ 2) (hshift x)
  rw [hint,
    dpoly_prime_finset_secondMoment_pos_iff_exists_coeff_ne_zero_on_vertical_interval
      P hP hAB]
  constructor
  · rintro ⟨p, _, hne⟩
    exact hne
  · intro hne
    exact ⟨hPne.choose, hPne.choose_spec, hne⟩

/-- The seed-gap coefficient: windowed-divisor carrier coefficient minus the
rough seed coefficient. -/
noncomputable def seedGapCoeff (lam : ℕ → ℝ) (N y : ℕ) : ℕ → ℝ := by
  classical
  exact fun n =>
    (∑ e ∈ n.divisors.filter (fun e => e ≤ y ∧ n ≤ N * e), lam e) -
      if (∀ q, q.Prime → q ∣ n → y < q) then (1 : ℝ) else 0

/-- On a singleton-window boundary element `p*d`, the actual seed-gap coefficient
is exactly the boundary weight `lam d`. -/
theorem seedGapCoeff_eq_lam_of_singleton_boundary (lam : ℕ → ℝ) {N y p d : ℕ}
    (hp : p.Prime) (hpy : y < p) (hd2 : 2 ≤ d) (hdy : d ≤ y) (hpN : p ≤ N)
    (hbig : N < p * d.minFac) :
    seedGapCoeff lam N y (p * d) = lam d := by
  classical
  have hd : 0 < d := by omega
  have hcar :=
    singleton_window_coeff_eq_lam lam hp hpy hd hdy hpN hbig
  have hnotrough : ¬ (∀ q, q.Prime → q ∣ p * d → y < q) :=
    not_rough_of_smooth_divisor hd2 hdy (dvd_mul_left d p)
  simp [seedGapCoeff, hcar, hnotrough]

/-- Rough primes have zero actual seed-gap coefficient when the rough seed is
normalized by `lam 1 = 1`. -/
theorem seedGapCoeff_prime_eq_zero_of_lam_one (lam : ℕ → ℝ) (hlam1 : lam 1 = 1)
    {N y p : ℕ} (hp : p.Prime) (hpy : y < p) (hpN : p ≤ N) (hy : 1 ≤ y) :
    seedGapCoeff lam N y p = 0 := by
  classical
  have hcar := prime_window_coeff_eq_lam_one lam hp hpy hpN hy
  have hrough : ∀ q, q.Prime → q ∣ p → y < q := by
    intro q hq hqp
    have hqp_eq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
    rwa [hqp_eq]
  have hif : (if (∀ q, q.Prime → q ∣ p → y < q) then (1 : ℝ) else 0) = 1 :=
    if_pos hrough
  simp [seedGapCoeff, hcar, hif, hlam1]

/-- The actual boundary seed-gap Dirichlet packet equals the constant boundary
packet on singleton-window support. -/
theorem seedGap_boundary_component_dpoly_eq (lam : ℕ → ℝ)
    {N y d : ℕ} (hd2 : 2 ≤ d) (hdy : d ≤ y)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hPy : ∀ p ∈ P, y < p) (hPN : ∀ p ∈ P, p ≤ N)
    (hbig : ∀ p ∈ P, N < p * d.minFac) (x : ℝ) :
    dpoly (seedGapCoeff lam N y) (P.image (fun p => p * d)) x =
      dpoly (fun _ => lam d) (P.image (fun p => p * d)) x := by
  classical
  unfold dpoly
  apply Finset.sum_congr rfl
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨p, hpP, rfl⟩
  simp [cterm, seedGapCoeff_eq_lam_of_singleton_boundary lam (hP p hpP)
    (hPy p hpP) hd2 hdy (hPN p hpP) (hbig p hpP)]

/-- The actual boundary seed-gap interval mass equals the prime-packet interval
mass after removing the common unimodular `d^{-it}` phase. -/
theorem seedGap_boundary_component_secondMoment_eq_prime_packet (lam : ℕ → ℝ)
    {N y d : ℕ} (hd2 : 2 ≤ d) (hdy : d ≤ y)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hPy : ∀ p ∈ P, y < p) (hPN : ∀ p ∈ P, p ≤ N)
    (hbig : ∀ p ∈ P, N < p * d.minFac)
    {A B : ℝ} :
    (∫ x in A..B,
        ‖dpoly (seedGapCoeff lam N y) (P.image (fun p => p * d)) x‖ ^ 2)
      = ∫ x in A..B, ‖dpoly (fun _ => lam d) P x‖ ^ 2 := by
  have hd : 0 < d := by omega
  apply intervalIntegral.integral_congr
  intro x _
  change ‖dpoly (seedGapCoeff lam N y) (P.image (fun p => p * d)) x‖ ^ 2 =
    ‖dpoly (fun _ => lam d) P x‖ ^ 2
  rw [seedGap_boundary_component_dpoly_eq lam hd2 hdy hP hPy hPN hbig x]
  exact congrArg (fun r : ℝ => r ^ 2)
    (dpoly_shift_norm (fun _ => lam d) (fun p hpP => (hP p hpP).pos) hd x)

/-- A finite set of primes is disjoint from its singleton-boundary image
`p ↦ p*d` when `d ≥ 2`. -/
theorem disjoint_primes_image_mul_of_two_le {P : Finset ℕ} {d : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hd2 : 2 ≤ d) :
    Disjoint P (P.image (fun p => p * d)) := by
  classical
  rw [Finset.disjoint_left]
  intro n hnP hnImg
  rcases Finset.mem_image.mp hnImg with ⟨p, hpP, hnpd⟩
  have hnprime : n.Prime := hP n hnP
  have hdvdn : d ∣ n := by
    rw [← hnpd]
    exact dvd_mul_left d p
  rcases (Nat.dvd_prime hnprime).mp hdvdn with hd1 | hdn
  · omega
  · rw [← hdn] at hnpd
    have hp1 : p = 1 := Nat.eq_of_mul_eq_mul_right (by omega : 0 < d) (by
      simpa [one_mul] using hnpd)
    exact (hP p hpP).ne_one hp1

/-- On the mixed support consisting of matched rough primes and singleton-boundary
terms, the actual seed-gap packet is exactly the boundary packet.  The rough
component disappears under `lam 1 = 1`. -/
theorem seedGap_rough_boundary_component_dpoly_eq_boundary (lam : ℕ → ℝ)
    (hlam1 : lam 1 = 1) {N y d : ℕ} (hy : 1 ≤ y) (hd2 : 2 ≤ d) (hdy : d ≤ y)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hPy : ∀ p ∈ P, y < p) (hPN : ∀ p ∈ P, p ≤ N)
    (hbig : ∀ p ∈ P, N < p * d.minFac) (x : ℝ) :
    dpoly (seedGapCoeff lam N y) (P ∪ P.image (fun p => p * d)) x =
      dpoly (fun _ => lam d) (P.image (fun p => p * d)) x := by
  classical
  have hdisj : Disjoint P (P.image (fun p => p * d)) :=
    disjoint_primes_image_mul_of_two_le hP hd2
  unfold dpoly
  rw [Finset.sum_union hdisj]
  have hroughZero : ∑ n ∈ P, cterm (seedGapCoeff lam N y) x n = 0 := by
    apply Finset.sum_eq_zero
    intro p hpP
    unfold cterm
    rw [seedGapCoeff_prime_eq_zero_of_lam_one lam hlam1 (hP p hpP) (hPy p hpP)
      (hPN p hpP) hy]
    simp
  rw [hroughZero, zero_add]
  apply Finset.sum_congr rfl
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨p, hpP, rfl⟩
  unfold cterm
  rw [seedGapCoeff_eq_lam_of_singleton_boundary lam (hP p hpP) (hPy p hpP)
    hd2 hdy (hPN p hpP) (hbig p hpP)]

/-- On the mixed rough-plus-boundary support, the actual seed-gap interval mass is
exactly the boundary prime-packet mass.  The matched rough component contributes
zero under `lam 1 = 1`. -/
theorem seedGap_rough_boundary_component_secondMoment_eq_prime_packet (lam : ℕ → ℝ)
    (hlam1 : lam 1 = 1) {N y d : ℕ} (hy : 1 ≤ y) (hd2 : 2 ≤ d) (hdy : d ≤ y)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hPy : ∀ p ∈ P, y < p) (hPN : ∀ p ∈ P, p ≤ N)
    (hbig : ∀ p ∈ P, N < p * d.minFac) {A B : ℝ} :
    (∫ x in A..B,
        ‖dpoly (seedGapCoeff lam N y) (P ∪ P.image (fun p => p * d)) x‖ ^ 2)
      = ∫ x in A..B, ‖dpoly (fun _ => lam d) P x‖ ^ 2 := by
  have hd : 0 < d := by omega
  apply intervalIntegral.integral_congr
  intro x _
  change ‖dpoly (seedGapCoeff lam N y) (P ∪ P.image (fun p => p * d)) x‖ ^ 2 =
    ‖dpoly (fun _ => lam d) P x‖ ^ 2
  rw [seedGap_rough_boundary_component_dpoly_eq_boundary lam hlam1 hy hd2 hdy hP hPy hPN
    hbig x]
  exact congrArg (fun r : ℝ => r ^ 2)
    (dpoly_shift_norm (fun _ => lam d) (fun p hpP => (hP p hpP).pos) hd x)

/-- **The actual boundary seed-gap packet is cancellation-free.**  On a finite
singleton-window packet `{p*d : p ∈ P}`, the real windowed-divisor carrier minus
the rough seed has positive interval `L²` mass on every nonempty vertical interval
iff the boundary coefficient `lam d` is nonzero.  This connects the arithmetic
singleton-window coefficient to the Hurwitz-backed prime-packet observable. -/
theorem seedGap_boundary_component_secondMoment_pos_iff (lam : ℕ → ℝ)
    {N y d : ℕ} (hd2 : 2 ≤ d) (hdy : d ≤ y)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hPne : P.Nonempty)
    (hPy : ∀ p ∈ P, y < p) (hPN : ∀ p ∈ P, p ≤ N)
    (hbig : ∀ p ∈ P, N < p * d.minFac)
    {A B : ℝ} (hAB : A < B) :
    (0 < ∫ x in A..B,
        ‖dpoly (seedGapCoeff lam N y) (P.image (fun p => p * d)) x‖ ^ 2) ↔
      lam d ≠ 0 := by
  rw [seedGap_boundary_component_secondMoment_eq_prime_packet lam hd2 hdy hP hPy hPN hbig,
    dpoly_prime_finset_secondMoment_pos_iff_exists_coeff_ne_zero_on_vertical_interval P hP hAB]
  constructor
  · rintro ⟨_p, _hpP, hne⟩
    exact hne
  · intro hne
    exact ⟨hPne.choose, hPne.choose_spec, hne⟩

/-- The actual boundary seed-gap packet vanishes on a nonempty vertical interval
exactly when the boundary weight `lam d` is zero.  This is the pointwise
constraint form of `seedGap_boundary_component_secondMoment_pos_iff`. -/
theorem seedGap_boundary_component_eq_zero_on_vertical_interval_iff (lam : ℕ → ℝ)
    {N y d : ℕ} (hd2 : 2 ≤ d) (hdy : d ≤ y)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hPne : P.Nonempty)
    (hPy : ∀ p ∈ P, y < p) (hPN : ∀ p ∈ P, p ≤ N)
    (hbig : ∀ p ∈ P, N < p * d.minFac)
    {A B : ℝ} (hAB : A < B) :
    (∀ t ∈ Set.Ioo A B,
        dpoly (seedGapCoeff lam N y) (P.image (fun p => p * d)) t = 0) ↔
      lam d = 0 := by
  have hd : 0 < d := by omega
  constructor
  · intro hzero
    have hprime_zero : ∀ t ∈ Set.Ioo A B, dpoly (fun _ => lam d) P t = 0 := by
      intro t ht
      have hactual := hzero t ht
      rw [seedGap_boundary_component_dpoly_eq lam hd2 hdy hP hPy hPN hbig t] at hactual
      have hnormP : ‖dpoly (fun _ => lam d) P t‖ = 0 := by
        rw [← dpoly_shift_norm (fun _ => lam d) (fun p hpP => (hP p hpP).pos) hd t]
        rw [hactual, norm_zero]
      exact norm_eq_zero.mp hnormP
    have hcoeff :=
      (dpoly_prime_finset_eq_zero_on_vertical_interval_iff_coeff_eq_zero P hP hAB).mp
        hprime_zero
    exact hcoeff hPne.choose hPne.choose_spec
  · intro hlam t _ht
    rw [seedGap_boundary_component_dpoly_eq lam hd2 hdy hP hPy hPN hbig t]
    unfold dpoly
    apply Finset.sum_eq_zero
    intro n _hn
    unfold cterm
    rw [hlam]
    simp

end RHTower
