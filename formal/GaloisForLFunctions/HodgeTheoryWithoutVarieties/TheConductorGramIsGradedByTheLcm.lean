import GaloisForLFunctions.HodgeTheoryWithoutVarieties.TheConductorsAreMoebiusGluedStars

/-!
# The conductor Gram is graded by the lcm

Two consequences of the star–conductor duality (`TheConductorsAreMoebiusGluedStars`).

* **Only pairs of the same lcm interact** (`sum_moebius_starPoleEnergy_eq_lcmPairs`,
  `sum_moebius_starPoleEnergy_completeWeil`). The pairs of divisors of `d` are partitioned by their
  lcm, which divides `d`. So the Möbius inversion of the star pole energies over the divisor lattice
  selects exactly the conductor pairs `(e, e')` with `lcm(e, e') = m`:

    `Σ_{d∣m} μ(m/d) d² W(pole|_{dℕ}) = Σ_{lcm(e,e') = m} √(φ(e)φ(e')) ⟨W r_e, r_{e'}⟩`.

  For the complete family the left side is the Möbius combination of the pole energies at the star
  resolutions. The finite-horizon conductor energy (`totient_mul_conductorEnergy_eq_lcm`) therefore
  has as its only correction the cross pairings of lcm `m`. For a prime `p` these are the pole
  couplings `(1, p)` and `(p, 1)`.
* **Star poles and conductors are bases of the horizon** (`eq_sum_starCoordinate_starPole`,
  `eq_sum_conductorCoordinate`). Every packet on `{1, …, N}` is `Σ_{d ≤ N} a_d pole|_{dℕ}` with
  `a_d = Σ_{k∣d} μ(d/k) √k x_k` (Möbius inversion of `√n x_n = Σ_{d∣n} a_d`), hence a combination
  of the Ramanujan packets `r_e`, `e ≤ N`. The conductor Gram over all conductors up to `N` is the
  whole form in another basis (`forall_qf_nonneg_iff_conductorGram`).
-/

noncomputable section

open Finset
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.ArithmeticLorentzianGeometry
open GaloisForLFunctions.BezoutValuationIncidence (moebiusReal)

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

/-! ### Only pairs of the same lcm interact -/

/-- The pairs of divisors of `l` with lcm `l`. -/
def lcmPairs (l : ℕ) : Finset (ℕ × ℕ) :=
  (l.divisors ×ˢ l.divisors).filter fun p => Nat.lcm p.1 p.2 = l

/-- Pairs of divisors of `d` are partitioned by their lcm. -/
theorem sum_divisors_prod_eq_sum_lcmPairs {d : ℕ} (hd : d ≠ 0) (F : ℕ × ℕ → ℝ) :
    ∑ p ∈ d.divisors ×ˢ d.divisors, F p = ∑ l ∈ d.divisors, ∑ p ∈ lcmPairs l, F p := by
  have hmaps : ∀ p ∈ d.divisors ×ˢ d.divisors, Nat.lcm p.1 p.2 ∈ d.divisors := by
    intro p hp
    simp only [mem_product, Nat.mem_divisors] at hp
    exact Nat.mem_divisors.mpr ⟨Nat.lcm_dvd hp.1.1 hp.2.1, hd⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun l hl => sum_congr ?_ fun _ _ => rfl
  have hld : l ∣ d := Nat.dvd_of_mem_divisors hl
  have hl0 : l ≠ 0 := ne_zero_of_dvd_ne_zero hd hld
  ext p
  simp only [mem_filter, mem_product, Nat.mem_divisors, lcmPairs]
  constructor
  · rintro ⟨-, hlcm⟩
    refine ⟨⟨⟨?_, hl0⟩, ?_, hl0⟩, hlcm⟩
    · rw [← hlcm]; exact Nat.dvd_lcm_left _ _
    · rw [← hlcm]; exact Nat.dvd_lcm_right _ _
  · rintro ⟨⟨⟨h1, -⟩, h2, -⟩, hlcm⟩
    exact ⟨⟨⟨h1.trans hld, hd⟩, h2.trans hld, hd⟩, hlcm⟩

/-- **Möbius inversion of pair sums selects the lcm.** -/
theorem sum_moebius_sum_divisors_prod {m : ℕ} (hm : 0 < m) (F : ℕ × ℕ → ℝ) :
    ∑ d ∈ m.divisors, moebiusReal (m / d) * ∑ p ∈ d.divisors ×ˢ d.divisors, F p =
      ∑ p ∈ lcmPairs m, F p := by
  have h : ∀ d ∈ m.divisors, moebiusReal (m / d) * ∑ p ∈ d.divisors ×ˢ d.divisors, F p =
      moebiusReal (m / d) * ∑ l ∈ d.divisors, ∑ p ∈ lcmPairs l, F p := fun d hd => by
    rw [sum_divisors_prod_eq_sum_lcmPairs (Nat.pos_of_mem_divisors hd).ne']
  rw [sum_congr rfl h]
  exact sum_moebius_sum_divisors hm fun l => ∑ p ∈ lcmPairs l, F p

/-- **Only pairs of lcm `m` interact.** For every form on the horizon, the `m`-th Möbius difference
of the star pole energies is the part of the conductor Gram on the pairs of lcm `m`. -/
theorem sum_moebius_starPoleEnergy_eq_lcmPairs {N : ℕ}
    (W : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) {m : ℕ} (hm : 0 < m) :
    ∑ d ∈ m.divisors, moebiusReal (m / d) * ((d : ℝ) ^ 2 * qf W (onHorizon N (starPole d))) =
      ∑ p ∈ lcmPairs m, Real.sqrt (p.1.totient : ℝ) * Real.sqrt (p.2.totient : ℝ) *
        conductorGram W p.1 p.2 := by
  have h : ∀ d ∈ m.divisors,
      moebiusReal (m / d) * ((d : ℝ) ^ 2 * qf W (onHorizon N (starPole d))) =
        moebiusReal (m / d) * ∑ p ∈ d.divisors ×ˢ d.divisors, Real.sqrt (p.1.totient : ℝ) *
          Real.sqrt (p.2.totient : ℝ) * conductorGram W p.1 p.2 := fun d hd => by
    rw [qf_starPole_eq_conductorGram W (Nat.pos_of_mem_divisors hd), sum_product]
  rw [sum_congr rfl h]
  exact sum_moebius_sum_divisors_prod hm _

/-- **Only pairs of lcm `m` interact, complete family.** The Möbius combination of the pole
energies at the star resolutions of the divisors of `m` is the conductor Gram on the pairs of
lcm `m`. -/
theorem sum_moebius_starPoleEnergy_completeWeil {φ : ℝ → ℝ} (hφ : EdgeHodgeTheory.Admissible φ)
    {c : ℝ} (hc : 0 < c) {N m : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    ∑ d ∈ m.divisors, moebiusReal (m / d) *
        ((d : ℝ) * completeWeilEnergy φ (starOverlap c N d) (N / d) (horizonPoleVector (N / d))) =
      ∑ p ∈ lcmPairs m, Real.sqrt (p.1.totient : ℝ) * Real.sqrt (p.2.totient : ℝ) *
        conductorGram (completeWeilMatrix φ c N) p.1 p.2 := by
  rw [← sum_moebius_starPoleEnergy_eq_lcmPairs _ hm]
  refine sum_congr rfl fun d hd => ?_
  congr 1
  rw [← qf_starPole_completeWeilMatrix hφ hc (Nat.pos_of_mem_divisors hd)
    ((Nat.divisor_le hd).trans hmN)]
  ring

/-- **The finite-horizon conductor energy, lcm form.** At every horizon, `φ(m) ⟨W r_m, r_m⟩` is the
Möbius combination of the star pole energies minus the cross pairings of lcm `m`. -/
theorem totient_mul_conductorEnergy_eq_lcm {φ : ℝ → ℝ} (hφ : EdgeHodgeTheory.Admissible φ)
    {c : ℝ} (hc : 0 < c) {N m : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    (m.totient : ℝ) * conductorGram (completeWeilMatrix φ c N) m m =
      ∑ d ∈ m.divisors, moebiusReal (m / d) *
          ((d : ℝ) * completeWeilEnergy φ (starOverlap c N d) (N / d)
            (horizonPoleVector (N / d))) -
        ∑ p ∈ (lcmPairs m).erase (m, m), Real.sqrt (p.1.totient : ℝ) *
          Real.sqrt (p.2.totient : ℝ) * conductorGram (completeWeilMatrix φ c N) p.1 p.2 := by
  have hmem : (m, m) ∈ lcmPairs m := by
    simp [lcmPairs, Nat.mem_divisors, hm.ne']
  rw [sum_moebius_starPoleEnergy_completeWeil hφ hc hm hmN, ← add_sum_erase _ _ hmem,
    add_sub_cancel_right, Real.mul_self_sqrt (Nat.cast_nonneg _)]

/-! ### Star poles and conductors are bases -/

/-- The star coordinates of a packet: `a_d = Σ_{k∣d} μ(d/k) √k F_k`. -/
def starCoordinate (F : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ k ∈ d.divisors, moebiusReal (d / k) * (Real.sqrt k * F k)

theorem sum_divisors_starCoordinate (F : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, starCoordinate F d = Real.sqrt n * F n := by
  refine (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)
    (f := starCoordinate F) (g := fun n => Real.sqrt n * F n)).mpr (fun d _ => ?_) n hn
  rw [Nat.sum_divisorsAntidiagonal' (fun a b => ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
    (Real.sqrt b * F b))]
  rfl

/-- **Star poles are a basis.** Every packet on `[1, N]` is a combination of the star poles. -/
theorem eq_sum_starCoordinate_starPole (F : ℕ → ℝ) {N n : ℕ} (hn : n ∈ Icc 1 N) :
    F n = ∑ d ∈ Icc 1 N, starCoordinate F d * starPole d n := by
  have hn0 : 0 < n := (mem_Icc.mp hn).1
  have hsq : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hn0)).ne'
  have hfilter : (Icc 1 N).filter (· ∣ n) = n.divisors := by
    ext d
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨-, h⟩
      exact ⟨h, hn0.ne'⟩
    · rintro ⟨h, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos h hn0, (Nat.le_of_dvd hn0 h).trans (mem_Icc.mp hn).2⟩, h⟩
  have h : ∑ d ∈ Icc 1 N, starCoordinate F d * starPole d n =
      (∑ d ∈ n.divisors, starCoordinate F d) * poleVector n := by
    simp only [starPole, starRestrict, mul_ite, mul_zero]
    rw [← sum_filter, hfilter, sum_mul]
  rw [h, sum_divisors_starCoordinate F hn0, poleVector]
  field_simp

/-- The conductor coordinates of a packet on `[1, N]`. -/
def conductorCoordinate (N : ℕ) (F : ℕ → ℝ) (e : ℕ) : ℝ :=
  ∑ d ∈ (Icc 1 N).filter (e ∣ ·), starCoordinate F d * (Real.sqrt (e.totient : ℝ) / d)

/-- **Conductors are a basis.** Every packet on `[1, N]` is a combination of the Ramanujan packets
of the conductors `e ≤ N`. -/
theorem eq_sum_conductorCoordinate (F : ℕ → ℝ) {N n : ℕ} (hn : n ∈ Icc 1 N) :
    F n = ∑ e ∈ Icc 1 N, conductorCoordinate N F e * ramanujanPoleProfile e n := by
  rw [eq_sum_starCoordinate_starPole F hn]
  have h1 : ∀ d ∈ Icc 1 N, starCoordinate F d * starPole d n =
      ∑ e ∈ d.divisors, starCoordinate F d * (Real.sqrt (e.totient : ℝ) / d) *
        ramanujanPoleProfile e n := by
    intro d hd
    rw [starPole_eq_sum_ramanujanPoleProfile (mem_Icc.mp hd).1, mul_sum]
    exact sum_congr rfl fun e _ => by ring
  rw [sum_congr rfl h1]
  simp only [conductorCoordinate, sum_mul]
  refine sum_comm' fun d e => ?_
  simp only [mem_Icc, mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd1, hdN⟩, hed, -⟩
    exact ⟨⟨⟨hd1, hdN⟩, hed⟩, Nat.pos_of_dvd_of_pos hed hd1, (Nat.le_of_dvd hd1 hed).trans hdN⟩
  · rintro ⟨⟨⟨hd1, hdN⟩, hed⟩, -, -⟩
    exact ⟨⟨hd1, hdN⟩, hed, by omega⟩

/-- A horizon packet extended by zero. -/
def horizonExtend {N : ℕ} (x : PrimeHorizonIndex N → ℝ) (n : ℕ) : ℝ :=
  if h : n ∈ Icc 1 N then x ⟨n, h⟩ else 0

/-- The form of a combination of conductors is its conductor Gram. -/
theorem qf_sum_conductors {N : ℕ} (W : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ)
    (S : Finset ℕ) (b : ℕ → ℝ) :
    qf W (∑ e ∈ S, b e • onHorizon N (ramanujanPoleProfile e)) =
      ∑ e ∈ S, ∑ e' ∈ S, b e * b e' * conductorGram W e e' :=
  qf_sum W S b _

/-- **The conductor Gram over all conductors is the whole form.** A form on the horizon is
positive semidefinite iff its conductor Gram over the conductors `e ≤ N` is. -/
theorem forall_qf_nonneg_iff_conductorGram {N : ℕ}
    (W : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) :
    (∀ x : PrimeHorizonIndex N → ℝ, 0 ≤ qf W x) ↔
      ∀ b : ℕ → ℝ, 0 ≤ ∑ e ∈ Icc 1 N, ∑ e' ∈ Icc 1 N, b e * b e' * conductorGram W e e' := by
  constructor
  · intro h b
    rw [← qf_sum_conductors]
    exact h _
  · intro h x
    have hx : x = ∑ e ∈ Icc 1 N,
        conductorCoordinate N (horizonExtend x) e • onHorizon N (ramanujanPoleProfile e) := by
      funext n
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, onHorizon]
      have hn := eq_sum_conductorCoordinate (horizonExtend x) n.2
      simp only [horizonExtend, dif_pos n.2] at hn
      exact hn
    rw [hx, qf_sum_conductors]
    exact h _

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
