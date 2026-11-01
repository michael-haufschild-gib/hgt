import GaloisForLFunctions.HodgeTheoryWithoutVarieties.TheLiouvilleProperty
import GaloisForLFunctions.HodgeTheoryWithoutVarieties.StarsOfTheCompleteWeilFamily
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFullPrimeMatrixHasRamanujanSpectralPoints
import GaloisForLFunctions.BezoutValuationIncidence.RamanujanLagCoefficientAndTotientQuotient

/-!
# Conductors are Möbius-glued stars

The vertex side of the divisibility complex is organized by **stars** (multiples of `d`). The
spectral side is organized by **conductors** (Ramanujan packets
`r_m(n) = c_m(n)/√(φ(m) n)`). The two are related by an exact triangular transform over the divisor
lattice:

* **Conductors from stars** (`ramanujanPoleProfile_eq_sum_starPole`): since
  `c_m(n) = Σ_{d ∣ (m, n)} μ(m/d) d`,
  `r_m = Σ_{d ∣ m} (μ(m/d) d/√φ(m)) · (pole packet on the star of d)`.
* **Stars from conductors** (`starPole_eq_sum_ramanujanPoleProfile`): since
  `Σ_{e ∣ d} c_e(n) = d [d ∣ n]`,
  `pole packet on the star of d = Σ_{e ∣ d} (√φ(e)/d) · r_e`.

For any symmetric form the energies transform accordingly (`qf_starPole_eq_conductorGram`): the
energy of the pole packet on the star of `d` is the conductor Gram of the divisors of `d`. For the
complete Weil family the star law identifies that energy with the pole energy at the star
resolution (`qf_starPole_completeWeilMatrix`):

  `d · W_{c⌊N/d⌋/N, ⌊N/d⌋}(pole) = Σ_{e, e' ∣ d} √(φ(e)φ(e')) ⟨W_{c,N} r_e, r_{e'}⟩`.

Möbius inversion over the divisor lattice then gives, **exactly at every horizon**
(`totient_mul_conductorEnergy_eq`):

  `φ(m) ⟨W_{c,N} r_m, r_m⟩ = Σ_{d ∣ m} μ(m/d) d · W_{c⌊N/d⌋/N, ⌊N/d⌋}(pole)
      − Σ_{d ∣ m} μ(m/d) Σ_{e ≠ e', e, e' ∣ d} √(φ(e)φ(e')) ⟨W_{c,N} r_e, r_{e'}⟩`.

The first sum is RAPT's completed conductor energy `φ(m)⁻¹ Σ_{d∣m} μ(m/d) d E(c/d)`, read at the
star resolutions. The second is the cross-conductor Gram among the divisors of `m`, which vanishes
in the limit by RAPT's asymptotic orthogonality of Ramanujan packets. So the limit gluing of RAPT is
exactly the Möbius dual of the star law. At finite `N` its only correction is the off-diagonal
conductor Gram.
-/

noncomputable section

open Finset
open scoped RealInnerProductSpace
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.ArithmeticLorentzianGeometry
open GaloisForLFunctions.BezoutValuationIncidence (ramanujanLagCoefficient moebiusReal)

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

/-! ### The pointwise duality -/

/-- The pole packet on the star of `d`: `n^{−1/2}` on the multiples of `d`, `0` elsewhere. -/
def starPole (d : ℕ) : ℕ → ℝ := starRestrict d poleVector

/-- The coefficient of the star of `d` in the conductor `m`: `μ(m/d) d/√φ(m)`. -/
def starCoeff (m d : ℕ) : ℝ := moebiusReal (m / d) * d / Real.sqrt (m.totient : ℝ)

/-- **Conductors from stars.** -/
theorem ramanujanPoleProfile_eq_sum_starPole {m : ℕ} (hm : 0 < m) (n : ℕ) :
    ramanujanPoleProfile m n = ∑ d ∈ m.divisors, starCoeff m d * starPole d n := by
  rw [ramanujanPoleProfile_eq_mul_poleVector, normalizedRamanujanMode_eq_coefficient hm,
    ramanujanLagCoefficient, sum_div, sum_mul]
  refine sum_congr rfl fun d _ => ?_
  simp only [starCoeff, starPole, starRestrict]
  split_ifs <;> ring

/-- **Stars from conductors.** -/
theorem starPole_eq_sum_ramanujanPoleProfile {d : ℕ} (hd : 0 < d) (n : ℕ) :
    starPole d n =
      ∑ e ∈ d.divisors, Real.sqrt (e.totient : ℝ) / d * ramanujanPoleProfile e n := by
  have hterm : ∀ e ∈ d.divisors, Real.sqrt (e.totient : ℝ) / d * ramanujanPoleProfile e n =
      (1 / d) * ramanujanLagCoefficient e n * poleVector n := by
    intro e he
    have he0 : 0 < e := Nat.pos_of_mem_divisors he
    have hφ : (0 : ℝ) < e.totient := by exact_mod_cast Nat.totient_pos.mpr he0
    rw [ramanujanPoleProfile_eq_mul_poleVector, normalizedRamanujanMode_eq_coefficient he0]
    field_simp
  rw [sum_congr rfl hterm, ← sum_mul, ← mul_sum,
    BezoutValuationIncidence.sum_divisors_ramanujanLagCoefficient]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [starPole, starRestrict]
  split_ifs
  · field_simp
  · ring

/-! ### Energies -/

section Bilinear

variable {ι κ : Type*} [Fintype ι]

theorem bil_sum_left (W : Matrix ι ι ℝ) (s : Finset κ) (a : κ → ℝ) (u : κ → ι → ℝ)
    (y : ι → ℝ) : bil W (∑ k ∈ s, a k • u k) y = ∑ k ∈ s, a k * bil W (u k) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bil]
  | insert k s hk ih => rw [sum_insert hk, sum_insert hk, bil_add_left, bil_smul_left, ih]

theorem bil_sum_right (W : Matrix ι ι ℝ) (x : ι → ℝ) (s : Finset κ) (a : κ → ℝ)
    (u : κ → ι → ℝ) : bil W x (∑ k ∈ s, a k • u k) = ∑ k ∈ s, a k * bil W x (u k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bil]
  | insert k s hk ih => rw [sum_insert hk, sum_insert hk, bil_add_right, bil_smul_right, ih]

/-- The quadratic form of a finite combination is its Gram expansion. -/
theorem qf_sum (W : Matrix ι ι ℝ) (s : Finset κ) (a : κ → ℝ) (u : κ → ι → ℝ) :
    qf W (∑ k ∈ s, a k • u k) = ∑ k ∈ s, ∑ l ∈ s, a k * a l * bil W (u k) (u l) := by
  rw [qf, bil_sum_left]
  refine sum_congr rfl fun k _ => ?_
  rw [bil_sum_right, mul_sum]
  exact sum_congr rfl fun l _ => by ring

end Bilinear

/-- A packet `ℕ → ℝ` read on the horizon. -/
def onHorizon (N : ℕ) (f : ℕ → ℝ) : PrimeHorizonIndex N → ℝ := fun n => f n

/-- The conductor Gram `⟨W r_e, r_{e'}⟩` of a form on the horizon. -/
def conductorGram {N : ℕ} (W : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ)
    (e e' : ℕ) : ℝ :=
  bil W (onHorizon N (ramanujanPoleProfile e)) (onHorizon N (ramanujanPoleProfile e'))

/-- **The energy of a star pole is the conductor Gram of the divisors.** For every form on the
horizon, `d² W(pole on the star of d) = Σ_{e, e' ∣ d} √(φ(e)φ(e')) ⟨W r_e, r_{e'}⟩`. -/
theorem qf_starPole_eq_conductorGram {N : ℕ}
    (W : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) {d : ℕ} (hd : 0 < d) :
    (d : ℝ) ^ 2 * qf W (onHorizon N (starPole d)) =
      ∑ e ∈ d.divisors, ∑ e' ∈ d.divisors,
        Real.sqrt (e.totient : ℝ) * Real.sqrt (e'.totient : ℝ) * conductorGram W e e' := by
  have hvec : onHorizon N (starPole d) = ∑ e ∈ d.divisors,
      (Real.sqrt (e.totient : ℝ) / d) • onHorizon N (ramanujanPoleProfile e) := by
    funext n
    rw [Finset.sum_apply]
    simp only [onHorizon, Pi.smul_apply, smul_eq_mul]
    exact starPole_eq_sum_ramanujanPoleProfile hd n
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [hvec, qf_sum, mul_sum]
  refine sum_congr rfl fun e _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun e' _ => ?_
  simp only [conductorGram]
  field_simp

/-- The star embedding of the lower-horizon pole is `√d` times the pole on the star. -/
theorem starEmbed_horizonPoleVector {d N : ℕ} (hd : 0 < d) (n : PrimeHorizonIndex N) :
    starEmbed d N (horizonPoleVector (N / d)) n = Real.sqrt d * starPole d n := by
  simp only [starEmbed, starPole, starRestrict, PiLp.toLp_apply]
  split_ifs with h
  · obtain ⟨a, ha⟩ := h
    have hn := mem_Icc.mp n.2
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | h0
      · simp at ha; omega
      · exact h0
    have haM : a ≤ N / d := (Nat.le_div_iff_mul_le hd).mpr (by rw [mul_comm, ← ha]; exact hn.2)
    rw [ha, Nat.mul_div_cancel_left a hd]
    simp only [primeHorizonExtension, dif_pos (mem_Icc.mpr ⟨ha1, haM⟩), horizonPoleVector,
      horizonProfileVector, PiLp.toLp_apply, poleVector]
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
    push_cast
    rw [Real.sqrt_mul hd0.le]
    field_simp
  · ring

/-- **The star law for the pole.** On the horizon `N`, the complete Weil energy of the pole packet
on the star of `d` is `1/d` times the pole energy of the family at the star resolution. -/
theorem qf_starPole_completeWeilMatrix {φ : ℝ → ℝ} (hφ : EdgeHodgeTheory.Admissible φ) {c : ℝ}
    (hc : 0 < c) {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    (d : ℝ) * qf (completeWeilMatrix φ c N) (onHorizon N (starPole d)) =
      completeWeilEnergy φ (starOverlap c N d) (N / d) (horizonPoleVector (N / d)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hsq : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr hd0).ne'
  have hvec : (fun n : PrimeHorizonIndex N => starEmbed d N (horizonPoleVector (N / d)) n) =
      Real.sqrt d • onHorizon N (starPole d) := by
    funext n
    rw [starEmbed_horizonPoleVector hd n]
    rfl
  rw [← completeWeilEnergy_starEmbed hφ.contDiff hφ.supp hc hd hdN, completeWeilEnergy_eq_qf,
    hvec]
  simp only [qf, bil_smul_left, bil_smul_right]
  rw [← mul_assoc, Real.mul_self_sqrt hd0.le]

/-- **The duality behind the limit gluing.** At every horizon, `d · W_{c_d, ⌊N/d⌋}(pole)` is the
conductor Gram of the divisors of `d`. -/
theorem starPoleEnergy_eq_conductorGram {φ : ℝ → ℝ} (hφ : EdgeHodgeTheory.Admissible φ) {c : ℝ}
    (hc : 0 < c) {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    (d : ℝ) * completeWeilEnergy φ (starOverlap c N d) (N / d) (horizonPoleVector (N / d)) =
      ∑ e ∈ d.divisors, ∑ e' ∈ d.divisors, Real.sqrt (e.totient : ℝ) *
        Real.sqrt (e'.totient : ℝ) * conductorGram (completeWeilMatrix φ c N) e e' := by
  rw [← qf_starPole_completeWeilMatrix hφ hc hd hdN, ← mul_assoc, ← sq,
    qf_starPole_eq_conductorGram _ hd]

/-! ### Möbius inversion: the completed conductor energy at finite horizon -/

/-- Möbius inversion of a divisor sum: `Σ_{d ∣ m} μ(m/d) Σ_{e ∣ d} f(e) = f(m)`. -/
theorem sum_moebius_sum_divisors {m : ℕ} (hm : 0 < m) (f : ℕ → ℝ) :
    ∑ d ∈ m.divisors, moebiusReal (m / d) * ∑ e ∈ d.divisors, f e = f m := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)
    (f := f) (g := fun n => ∑ e ∈ n.divisors, f e)).mp (fun _ _ => rfl) m hm
  rw [← h, Nat.sum_divisorsAntidiagonal' (fun a b => ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
    ∑ e ∈ b.divisors, f e)]
  rfl

/-- **The completed conductor energy at finite horizon.** For every conductor `m`, at every
horizon, `φ(m) ⟨W r_m, r_m⟩` is the Möbius combination of the pole energies at the star
resolutions of the divisors of `m`, minus the off-diagonal conductor Gram among those divisors. -/
theorem totient_mul_conductorEnergy_eq {φ : ℝ → ℝ} (hφ : EdgeHodgeTheory.Admissible φ) {c : ℝ}
    (hc : 0 < c) {N m : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    (m.totient : ℝ) * conductorGram (completeWeilMatrix φ c N) m m =
      ∑ d ∈ m.divisors, moebiusReal (m / d) *
          ((d : ℝ) * completeWeilEnergy φ (starOverlap c N d) (N / d)
            (horizonPoleVector (N / d))) -
        ∑ d ∈ m.divisors, moebiusReal (m / d) *
          ∑ e ∈ d.divisors, ∑ e' ∈ d.divisors.erase e, Real.sqrt (e.totient : ℝ) *
            Real.sqrt (e'.totient : ℝ) * conductorGram (completeWeilMatrix φ c N) e e' := by
  set G := conductorGram (completeWeilMatrix φ c N)
  have hstar : ∀ d ∈ m.divisors,
      (d : ℝ) * completeWeilEnergy φ (starOverlap c N d) (N / d) (horizonPoleVector (N / d)) =
        ∑ e ∈ d.divisors, (e.totient : ℝ) * G e e +
          ∑ e ∈ d.divisors, ∑ e' ∈ d.divisors.erase e,
            Real.sqrt (e.totient : ℝ) * Real.sqrt (e'.totient : ℝ) * G e e' := by
    intro d hdm
    have hd : 0 < d := Nat.pos_of_mem_divisors hdm
    have hdN : d ≤ N := (Nat.divisor_le hdm).trans hmN
    rw [starPoleEnergy_eq_conductorGram hφ hc hd hdN, ← sum_add_distrib]
    refine sum_congr rfl fun e he => ?_
    rw [← sum_erase_add _ _ he, add_comm]
    congr 1
    rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
  rw [sum_congr rfl fun d hd => by rw [hstar d hd], ← sum_sub_distrib]
  simp only [mul_add, add_sub_cancel_right]
  exact (sum_moebius_sum_divisors hm fun e => (e.totient : ℝ) * G e e).symm

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
