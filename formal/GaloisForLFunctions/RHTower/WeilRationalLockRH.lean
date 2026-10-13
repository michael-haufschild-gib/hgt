import GaloisForLFunctions.RHTower.WeilAlmostPeriodicLockCoefficients
import GaloisForLFunctions.RHTower.LimitPeriodicProducerRH

/-!
# Rational almost-periodic locks force the Riemann hypothesis

**Theorem** (`rationalLock_riemannHypothesis`). Let `G` be a Herglotz producer for the weights
`lam` with lower-line lock

`G(1 − s) = V(s) G(s)`,   `V(s) = Σ_j c_j r_j^{−(s−½)}`,

with positive rational frequencies `r_j` (denominators unbounded) and

`Σ_j |c_j| max(1, r_j^{−1}) √den(r_j) 8^{ω(den r_j)} < ∞`.

Then the Riemann hypothesis holds. Since `8^{ω(d)} ≪_ε d^ε`, the weight `den(r_j)^{½+ε}` suffices.
This closes the two-sided rational spectra with unbounded denominators. The bounded case is
`bounded_denominator_lock_riemannHypothesis`.

**Proof.**
* `apLock_coefficients`: `a(n) = Σ_{0 < m r_j ≤ 1} a(m) c_j √r_j e(n m r_j)`.
* *Grouping by denominators* (`lockExpCoeff_eq_tsum_ratLockPart`). The terms with `den(m r_j) = q+1`
  form a function `Ψ_q` of period `q + 1`, because `e(n y)` depends only on `n mod den(y)`
  (`cexp_ratCast_mul_mod`). Its size is `B_q = Σ_{den = q+1} |w(p)|` (`norm_ratLockPart_le`).
* *Weights* (`summable_ratLockMass_weight`). We have `den(m r_j) | den(r_j)`, and `√d 8^{ω(d)}` is
  monotone under divisibility. Below height one
  `|w(m, j)| ≤ |a(m)| m^{−3/2} |c_j| max(1, r_j^{−1})`.
  So `Σ_q √(q+1) 8^{ω(q+1)} B_q < ∞`.
* `limitPeriodic_producer_riemannHypothesis` (which uses `limitPeriodic_exp_single_character`).
-/

open Complex Filter Topology Set

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity
  HamburgerTwisted WeilSpectral CharacterZeroPlanting

noncomputable section

/-! ## Rational lock points -/

/-- The rational lock point `m r_j` of the pair `(m, j)`. -/
def ratPt (r : ℕ → ℚ) (p : ℕ × ℕ) : ℚ := (p.1 : ℚ) * r p.2

theorem lockPoint_ratCast (r : ℕ → ℚ) (p : ℕ × ℕ) :
    lockPoint (fun j => (r j : ℝ)) p = ((ratPt r p : ℚ) : ℝ) := by
  unfold lockPoint ratPt; push_cast; ring

theorem den_ratPt_dvd (r : ℕ → ℚ) (p : ℕ × ℕ) : (ratPt r p).den ∣ (r p.2).den := by
  have h := Rat.mul_den_dvd (p.1 : ℚ) (r p.2)
  rwa [Rat.den_natCast, one_mul] at h

/-- `e(n y)` depends only on `n` modulo the denominator of `y`. -/
theorem cexp_ratCast_mul_mod (y : ℚ) (n : ℕ) :
    cexp (2 * Real.pi * I * (((y : ℝ)) : ℂ) * ((n % y.den : ℕ) : ℂ)) =
      cexp (2 * Real.pi * I * (((y : ℝ)) : ℂ) * (n : ℂ)) := by
  have hn : (n : ℂ) = (y.den : ℂ) * ((n / y.den : ℕ) : ℂ) + ((n % y.den : ℕ) : ℂ) := by
    exact_mod_cast (Nat.div_add_mod n y.den).symm
  have hy : ((y : ℝ) : ℂ) * (y.den : ℂ) = (y.num : ℂ) := by
    have := Rat.mul_den_eq_num y
    rw [Complex.ofReal_ratCast]
    exact_mod_cast this
  have e : 2 * Real.pi * I * (((y : ℝ)) : ℂ) * (n : ℂ) =
      2 * Real.pi * I * (((y : ℝ)) : ℂ) * ((n % y.den : ℕ) : ℂ) +
        ((y.num * (n / y.den : ℕ) : ℤ) : ℂ) * (2 * Real.pi * I) := by
    rw [hn, Int.cast_mul, Int.cast_natCast, ← hy]; ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ## The limit-periodic decomposition -/

/-- The weight `K(d) = √d 8^{ω(d)}`. -/
def denWeight (d : ℕ) : ℝ := Real.sqrt d * 8 ^ d.primeFactors.card

theorem denWeight_nonneg (d : ℕ) : 0 ≤ denWeight d := by unfold denWeight; positivity

theorem denWeight_mono {d d' : ℕ} (h : d ∣ d') (hd' : d' ≠ 0) : denWeight d ≤ denWeight d' := by
  unfold denWeight
  have h1 : Real.sqrt d ≤ Real.sqrt d' :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hd') h)
  have h2 : (8 : ℝ) ^ d.primeFactors.card ≤ 8 ^ d'.primeFactors.card :=
    pow_le_pow_right₀ (by norm_num) (Finset.card_le_card (Nat.primeFactors_mono h hd'))
  exact mul_le_mul h1 h2 (by positivity) (Real.sqrt_nonneg _)

/-- The condition `0 < m r_j ≤ 1` on a pair. -/
def ratCond (r : ℕ → ℚ) (p : ℕ × ℕ) : Prop :=
  0 < lockPoint (fun j => (r j : ℝ)) p ∧ lockPoint (fun j => (r j : ℝ)) p ≤ 1

open Classical in
/-- The part of level `q + 1`: the lock points of denominator `q + 1`. -/
def ratLockPart (a c : ℕ → ℂ) (r : ℕ → ℚ) (q : ℕ) (x : ZMod (q + 1)) : ℂ :=
  ∑' p : ℕ × ℕ, if ratCond r p ∧ (ratPt r p).den = q + 1 then
    lockWeight a c (fun j => (r j : ℝ)) p *
      cexp (2 * Real.pi * I * (((ratPt r p : ℚ) : ℝ) : ℂ) * (x.val : ℂ)) else 0

open Classical in
/-- The size `B_q = Σ_{den = q+1} |w(p)|` of the part of level `q + 1`. -/
def ratLockMass (a c : ℕ → ℂ) (r : ℕ → ℚ) (q : ℕ) : ℝ :=
  ∑' p : ℕ × ℕ, if ratCond r p ∧ (ratPt r p).den = q + 1 then
    ‖lockWeight a c (fun j => (r j : ℝ)) p‖ else 0

theorem one_le_denWeight {d : ℕ} (hd : d ≠ 0) : 1 ≤ denWeight d := by
  unfold denWeight
  have h1 : 1 ≤ Real.sqrt d :=
    Real.one_le_sqrt.mpr (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd)
  have h2 : (1 : ℝ) ≤ 8 ^ d.primeFactors.card := one_le_pow₀ (by norm_num)
  nlinarith

theorem den_ratPt_eq_iff (r : ℕ → ℚ) (p : ℕ × ℕ) (q : ℕ) :
    (ratPt r p).den = q + 1 ↔ q = (ratPt r p).den - 1 := by
  have := (ratPt r p).den_pos
  omega

open Classical in
theorem norm_ratLockPart_le {a c : ℕ → ℂ} {r : ℕ → ℚ} (hu : ∀ j, 0 < (r j : ℝ))
    (ha0 : a 0 = 0) (ha : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-(3 / 2 : ℝ)))
    (hc : Summable fun j => ‖c j‖ * max 1 ((r j : ℝ))⁻¹) (q : ℕ) (x : ZMod (q + 1)) :
    ‖ratLockPart a c r q x‖ ≤ ratLockMass a c r q := by
  have hW := summable_norm_lockWeight_le_one hu ha0 ha hc
  have hb : ∀ p : ℕ × ℕ, ‖(if ratCond r p ∧ (ratPt r p).den = q + 1 then
      lockWeight a c (fun j => (r j : ℝ)) p *
        cexp (2 * Real.pi * I * (((ratPt r p : ℚ) : ℝ) : ℂ) * (x.val : ℂ)) else 0)‖ ≤
      if ratCond r p ∧ (ratPt r p).den = q + 1 then
        ‖lockWeight a c (fun j => (r j : ℝ)) p‖ else 0 := by
    intro p
    split_ifs
    · rw [norm_mul, norm_cexp_two_pi_I_mul, mul_one]
    · rw [norm_zero]
  have hs : Summable fun p : ℕ × ℕ => if ratCond r p ∧ (ratPt r p).den = q + 1 then
      ‖lockWeight a c (fun j => (r j : ℝ)) p‖ else 0 :=
    Summable.of_nonneg_of_le (fun p => by split_ifs; exacts [norm_nonneg _, le_rfl])
      (fun p => by
        unfold ratCond
        split_ifs with h1 h2
        · exact le_rfl
        · exact absurd h1.1 h2
        · exact norm_nonneg _
        · exact le_rfl) hW
  exact (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs)).trans
    ((Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs).tsum_le_tsum hb hs)

open Classical in
/-- The exponential term `[0 < y_p ≤ 1] w(p) e(n y_p)` at a rational lock point. -/
def ratExpTerm (a c : ℕ → ℂ) (r : ℕ → ℚ) (n : ℕ) (p : ℕ × ℕ) : ℂ :=
  if ratCond r p then lockWeight a c (fun j => (r j : ℝ)) p *
    cexp (2 * Real.pi * I * (((ratPt r p : ℚ) : ℝ) : ℂ) * (n : ℂ)) else 0

open Classical in
/-- The norm `[0 < y_p ≤ 1] |w(p)|`. -/
def ratNormTerm (a c : ℕ → ℂ) (r : ℕ → ℚ) (p : ℕ × ℕ) : ℝ :=
  if ratCond r p then ‖lockWeight a c (fun j => (r j : ℝ)) p‖ else 0

theorem norm_ratExpTerm_le (a c : ℕ → ℂ) (r : ℕ → ℚ) (n : ℕ) (p : ℕ × ℕ) :
    ‖ratExpTerm a c r n p‖ ≤ ratNormTerm a c r p := by
  unfold ratExpTerm ratNormTerm
  split_ifs
  · rw [norm_mul, norm_cexp_two_pi_I_mul, mul_one]
  · rw [norm_zero]

theorem ratNormTerm_nonneg (a c : ℕ → ℂ) (r : ℕ → ℚ) (p : ℕ × ℕ) : 0 ≤ ratNormTerm a c r p := by
  unfold ratNormTerm; split_ifs
  · exact norm_nonneg _
  · exact le_rfl

open Classical in
theorem ratLockPart_natCast (a c : ℕ → ℂ) (r : ℕ → ℚ) (q n : ℕ) :
    ratLockPart a c r q (n : ZMod (q + 1)) = ∑' p, if q = (ratPt r p).den - 1 then
      ratExpTerm a c r n p else 0 := by
  unfold ratLockPart
  refine tsum_congr fun p => ?_
  unfold ratExpTerm
  by_cases hq : q = (ratPt r p).den - 1
  · have hd : (ratPt r p).den = q + 1 := (den_ratPt_eq_iff r p q).mpr hq
    rw [if_pos hq]
    by_cases hcnd : ratCond r p
    · rw [if_pos ⟨hcnd, hd⟩, if_pos hcnd, ZMod.val_natCast, ← hd, cexp_ratCast_mul_mod]
    · rw [if_neg (fun h => hcnd h.1), if_neg hcnd]
  · rw [if_neg hq, if_neg (fun h => hq ((den_ratPt_eq_iff r p q).mp h.2))]

/-- **The decomposition by denominators.** `b_+(n) = Σ_q Ψ_q(n)`. -/
theorem lockExpCoeff_eq_tsum_ratLockPart {a c : ℕ → ℂ} {r : ℕ → ℚ} (hu : ∀ j, 0 < (r j : ℝ))
    (ha0 : a 0 = 0) (ha : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-(3 / 2 : ℝ)))
    (hc : Summable fun j => ‖c j‖ * max 1 ((r j : ℝ))⁻¹) (n : ℕ) :
    lockExpCoeff a c (fun j => (r j : ℝ)) 1 n = ∑' q, ratLockPart a c r q (n : ZMod (q + 1)) := by
  have hW : Summable (ratNormTerm a c r) :=
    (summable_norm_lockWeight_le_one hu ha0 ha hc).congr fun p => by
      unfold ratNormTerm ratCond
      split_ifs <;> rfl
  have hfib : ∀ p : ℕ × ℕ, HasSum (fun q : ℕ => if q = (ratPt r p).den - 1 then
      ratNormTerm a c r p else 0) (ratNormTerm a c r p) := fun p =>
    hasSum_ite_eq ((ratPt r p).den - 1) (ratNormTerm a c r p)
  have hbs : Summable fun x : (ℕ × ℕ) × ℕ => if x.2 = (ratPt r x.1).den - 1 then
      ratNormTerm a c r x.1 else 0 := by
    refine (summable_prod_of_nonneg fun x => ?_).mpr ⟨fun p => (hfib p).summable, ?_⟩
    · split_ifs
      · exact ratNormTerm_nonneg a c r _
      · exact le_rfl
    · exact hW.congr fun p => ((hfib p).tsum_eq).symm
  have hsum : Summable (Function.uncurry fun (p : ℕ × ℕ) (q : ℕ) =>
      if q = (ratPt r p).den - 1 then ratExpTerm a c r n p else 0) := by
    refine Summable.of_norm_bounded hbs fun x => ?_
    simp only [Function.uncurry]
    split_ifs
    · exact norm_ratExpTerm_le a c r n x.1
    · rw [norm_zero]
  rw [tsum_congr fun q => ratLockPart_natCast a c r q n, hsum.tsum_comm]
  unfold lockExpCoeff
  refine tsum_congr fun p => ?_
  rw [tsum_ite_eq ((ratPt r p).den - 1) (fun _ => ratExpTerm a c r n p)]
  unfold ratExpTerm ratCond
  split_ifs
  · rw [one_mul, lockPoint_ratCast]
  · rfl

/-- **The weight of the decomposition.** `Σ_q √(q+1) 8^{ω(q+1)} B_q < ∞` when
`Σ_j |c_j| max(1, r_j^{−1}) √den(r_j) 8^{ω(den r_j)} < ∞`. -/
theorem summable_ratLockMass_weight {a c : ℕ → ℂ} {r : ℕ → ℚ} (hu : ∀ j, 0 < (r j : ℝ))
    (ha0 : a 0 = 0) (ha : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-(3 / 2 : ℝ)))
    (hcw : Summable fun j => ‖c j‖ * max 1 ((r j : ℝ))⁻¹ * denWeight (r j).den) :
    Summable fun q : ℕ =>
      Real.sqrt ((q : ℝ) + 1) * 8 ^ (q + 1).primeFactors.card * ratLockMass a c r q := by
  set E : (ℕ × ℕ) × ℕ → ℝ := fun x => if x.2 = (ratPt r x.1).den - 1 then
    ratNormTerm a c r x.1 * denWeight (ratPt r x.1).den else 0 with hE
  have hE0 : 0 ≤ E := fun x => by
    simp only [hE]; split_ifs
    · exact mul_nonneg (ratNormTerm_nonneg a c r _) (denWeight_nonneg _)
    · exact le_rfl
  have hfib : ∀ p : ℕ × ℕ, HasSum (fun q : ℕ => E (p, q))
      (ratNormTerm a c r p * denWeight (ratPt r p).den) := fun p =>
    hasSum_ite_eq ((ratPt r p).den - 1) (ratNormTerm a c r p * denWeight (ratPt r p).den)
  have hD : Summable fun p : ℕ × ℕ =>
      ‖a p.1‖ * (p.1 : ℝ) ^ (-(3 / 2 : ℝ)) *
        (‖c p.2‖ * max 1 ((r p.2 : ℝ))⁻¹ * denWeight (r p.2).den) :=
    Summable.mul_of_nonneg ha hcw
      (fun n => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (fun j => mul_nonneg (mul_nonneg (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _)))
        (denWeight_nonneg _))
  have hpb : ∀ p : ℕ × ℕ, ratNormTerm a c r p * denWeight (ratPt r p).den ≤
      ‖a p.1‖ * (p.1 : ℝ) ^ (-(3 / 2 : ℝ)) *
        (‖c p.2‖ * max 1 ((r p.2 : ℝ))⁻¹ * denWeight (r p.2).den) := by
    intro p
    have hK := denWeight_mono (den_ratPt_dvd r p) (r p.2).den_nz
    have hN : ratNormTerm a c r p ≤ lockDom a c (fun j => (r j : ℝ)) p := by
      unfold ratNormTerm
      split_ifs with h
      · exact norm_lockWeight_le_lockDom hu ha0 h.2
      · exact lockDom_nonneg _ _ _ p
    calc ratNormTerm a c r p * denWeight (ratPt r p).den
        ≤ lockDom a c (fun j => (r j : ℝ)) p * denWeight (r p.2).den :=
          mul_le_mul hN hK (denWeight_nonneg _) (lockDom_nonneg _ _ _ p)
      _ = ‖a p.1‖ * (p.1 : ℝ) ^ (-(3 / 2 : ℝ)) *
            (‖c p.2‖ * max 1 ((r p.2 : ℝ))⁻¹ * denWeight (r p.2).den) := by
          unfold lockDom; ring
  have hEs : Summable E :=
    (summable_prod_of_nonneg hE0).mpr ⟨fun p => (hfib p).summable,
      Summable.of_nonneg_of_le (fun p => tsum_nonneg fun q => hE0 (p, q))
        (fun p => ((hfib p).tsum_eq).le.trans (hpb p)) hD⟩
  have hsw : Summable (E ∘ Equiv.prodComm ℕ (ℕ × ℕ)) :=
    (Equiv.prodComm ℕ (ℕ × ℕ)).summable_iff.mpr hEs
  refine hsw.prod.congr fun q => ?_
  unfold ratLockMass
  rw [← tsum_mul_left]
  refine tsum_congr fun p => ?_
  simp only [Function.comp, Equiv.prodComm_apply, Prod.swap, hE]
  unfold ratNormTerm
  by_cases hq : q = (ratPt r p).den - 1
  · have hd : (ratPt r p).den = q + 1 := (den_ratPt_eq_iff r p q).mpr hq
    rw [if_pos hq]
    have hdw : denWeight (ratPt r p).den =
        Real.sqrt ((q : ℝ) + 1) * 8 ^ (q + 1).primeFactors.card := by
      rw [hd, denWeight]; push_cast; ring
    by_cases hcnd : ratCond r p
    · rw [if_pos hcnd, if_pos ⟨hcnd, hd⟩, hdw]; ring
    · rw [if_neg hcnd, if_neg (fun h => hcnd h.1)]; ring
  · rw [if_neg hq, if_neg (fun h => hq ((den_ratPt_eq_iff r p q).mp h.2)), mul_zero]

/-- **Rational almost-periodic locks force the Riemann hypothesis.** Let `G` be a Herglotz producer
for the weights `lam` with lower-line lock `G(1 − s) = V(s) G(s)`, `V(s) = Σ_j c_j r_j^{−(s−½)}`,
with positive rational frequencies `r_j` and
`Σ_j |c_j| max(1, r_j^{−1}) √den(r_j) 8^{ω(den r_j)} < ∞`. Then the Riemann hypothesis holds. -/
theorem rationalLock_riemannHypothesis {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {c : ℕ → ℂ} {r : ℕ → ℚ} (hr : ∀ j, 0 < r j)
    (hcw : Summable fun j => ‖c j‖ * max 1 ((r j : ℝ))⁻¹ * denWeight (r j).den)
    (hlock : ∀ τ : ℝ, τ < 0 →
      G (1 - lineS τ) = apLock c (fun j => (r j : ℝ)) (lineS τ) * G (lineS τ)) :
    RiemannHypothesis := by
  set a := dirichletExp (lamLog lam) with ha
  have hu : ∀ j, 0 < ((r j : ℚ) : ℝ) := fun j => Rat.cast_pos.mpr (hr j)
  have hc : Summable fun j => ‖c j‖ * max 1 ((r j : ℝ))⁻¹ :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _)))
      (fun j => le_mul_of_one_le_right
        (mul_nonneg (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _)))
        (one_le_denWeight (r j).den_nz)) hcw
  have ha0 : a 0 = 0 := dirichletExp_zero
  have ha32 := summable_norm_mul_rpow_dirichletExp hsl (σ := 3 / 2) (by norm_num)
  have hcoef := apLock_coefficients hsl hΦre hid hGc hGd hG2 hu hc hlock
  exact limitPeriodic_producer_riemannHypothesis hsl hΦd hid hGc hGd hG2
    (Ψ := ratLockPart a c r) (B := ratLockMass a c r)
    (fun q x => norm_ratLockPart_le hu ha0 ha32 hc q x)
    (summable_ratLockMass_weight hu ha0 ha32 hcw)
    (fun n hn => (hcoef n hn).trans (lockExpCoeff_eq_tsum_ratLockPart hu ha0 ha32 hc n))

end

end AbelianTwist

end RHTower
