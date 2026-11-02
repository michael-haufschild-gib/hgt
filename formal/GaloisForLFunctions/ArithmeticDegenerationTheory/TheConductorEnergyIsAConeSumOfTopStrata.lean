import GaloisForLFunctions.ArithmeticDegenerationTheory.TheWeightStringsOfTheRescaledLimit
import GaloisForLFunctions.HodgeTheoryWithoutVarieties.TheGcdStratification

/-!
# The conductor energy is a cone sum of top strata

Two exact structures meet here. The dilation monoid acts on conductors by lowering
(`TheDilationsLowerTheConductor`), and the complete Weil form is the sum over `g` of the coprime
(top-stratum) parts of its stars at the star resolutions (HWV gcd stratification). Together they
reconstruct the energy of a graded piece from top-stratum data alone.

* **The monodromy in closed form** (`ramanujanLagCoefficient_mul_eq`): for all `m, g ≥ 1`,
  `c_m(gn) = (φ(m)/φ(m/(m,g))) c_{m/(m,g)}(n)`. The dilation by `g` lowers the conductor to
  `m/gcd(m, g)` with weight `φ(m)/φ(m/(m,g))`; the prime law is the case `g = p`, and the weights
  telescope along a factorization of `g`.
* **In the pole gauge** (`ramanujanPoleProfile_mul_eq`):
  `r_m(gn) = θ_g(m) r_{m/(m,g)}(n)`, `θ_g(m) = √(φ(m)/(g φ(m/(m,g))))`.
* **The cone expansion** (`completeWeilEnergy_ramanujan_cone_expansion`): for every admissible
  profile,
  `⟨W_{c,N} r_e, r_e⟩ = (log N)⁻¹ Σ_{g ≤ N} θ_g(e)² · Top_{c_g, ⌊N/g⌋}(R_{e/(e,g)})`,
  where `Top_{c,M}(y) = Σ_{(a,b)=1} W_{c,M}(a,b) y_a y_b` is the top-stratum (coprime) energy and
  `R_m` the Ramanujan vector at the lower horizon.

So the energy of every graded piece is a positive combination, over the cone of dilations, of
top-stratum energies of lowered conductors at the star resolutions. The polarization of the graded
pieces is reconstructed from the extension data of the top stratum: the arithmetic form of the
statement that the limiting structure is determined by its graded pieces and extension data.
-/

noncomputable section

open Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticDegenerationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory HodgeTheoryWithoutVarieties

/-- The prime dilation weight is a totient ratio: `w_p(m) = φ(m)/φ(ℓ_p m)`. -/
theorem dilationWeight_eq_totient_ratio {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    dilationWeight p m = (m.totient : ℝ) / (conductorLower p m).totient := by
  by_cases hpm : p ∣ m
  · have hm' : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm hpm) hp.pos
    have ht : (0 : ℝ) < (m / p).totient := by exact_mod_cast Nat.totient_pos.mpr hm'
    rw [conductorLower_of_dvd hpm, totient_prime_mul_of_dvd hp hpm, mul_div_cancel_right₀ _ ht.ne']
    simp [dilationWeight, hpm]
  · have ht : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
    rw [conductorLower_of_not_dvd hpm, div_self ht.ne']
    simp [dilationWeight, hpm]

/-- Lowering by `p` and then by `g'` is lowering by `pg'`. -/
theorem conductorLower_div_gcd {p m : ℕ} (hp : p.Prime) (g' : ℕ) :
    conductorLower p m / Nat.gcd (conductorLower p m) g' = m / Nat.gcd m (p * g') := by
  by_cases hpm : p ∣ m
  · rw [conductorLower_of_dvd hpm]
    conv_rhs => rw [← Nat.mul_div_cancel' hpm, Nat.gcd_mul_left, Nat.mul_div_mul_left _ _ hp.pos]
  · rw [conductorLower_of_not_dvd hpm]
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
    rw [Nat.Coprime.gcd_mul_left_cancel_right g' hcop]

/-- **The monodromy in closed form.** `c_m(gn) = (φ(m)/φ(m/(m,g))) c_{m/(m,g)}(n)`. -/
theorem ramanujanLagCoefficient_mul_eq : ∀ (g m : ℕ), 0 < g → 0 < m → ∀ n : ℕ,
    ramanujanLagCoefficient m (g * n) =
      (m.totient : ℝ) / (m / Nat.gcd m g).totient * ramanujanLagCoefficient (m / Nat.gcd m g) n := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro m hg hm n
    rcases Nat.lt_or_ge 1 g with hg1 | hg1
    · set p := g.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      set g' := g / p
      have hgg : g = p * g' := (Nat.mul_div_cancel' (Nat.minFac_dvd g)).symm
      have hg' : 0 < g' := Nat.div_pos (Nat.minFac_le hg) hp.pos
      have hlt : g' < g := Nat.div_lt_self hg hp.one_lt
      have hl : 0 < conductorLower p m := by
        unfold conductorLower
        split_ifs with h
        · exact Nat.div_pos (Nat.le_of_dvd hm h) hp.pos
        · exact hm
      rw [hgg, mul_assoc, ramanujanLagCoefficient_prime_mul_eq hp hm,
        ih g' hlt (conductorLower p m) hg' hl n, conductorLower_div_gcd hp g',
        dilationWeight_eq_totient_ratio hp hm]
      have ht : (0 : ℝ) < (conductorLower p m).totient := by exact_mod_cast Nat.totient_pos.mpr hl
      field_simp
    · have : g = 1 := by omega
      subst this
      have ht : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
      simp [div_self ht.ne']

/-- The general normalized dilation factor `θ_g(m) = √(φ(m)/(g φ(m/(m,g))))`. -/
def coneFactor (g m : ℕ) : ℝ := Real.sqrt ((m.totient : ℝ) / (g * (m / Nat.gcd m g).totient))

/-- **The monodromy in the pole gauge.** `r_m(gn) = θ_g(m) r_{m/(m,g)}(n)`. -/
theorem ramanujanPoleProfile_mul_eq {g m : ℕ} (hg : 0 < g) (hm : 0 < m) (n : ℕ) :
    ramanujanPoleProfile m (g * n) = coneFactor g m * ramanujanPoleProfile (m / Nat.gcd m g) n := by
  set L := m / Nat.gcd m g
  have hL : 0 < L := Nat.div_pos (Nat.le_of_dvd hm (Nat.gcd_dvd_left m g)) (Nat.gcd_pos_of_pos_left g hm)
  have htm : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have htL : (0 : ℝ) < L.totient := by exact_mod_cast Nat.totient_pos.mpr hL
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  simp only [ramanujanPoleProfile, normalizedRamanujanMode,
    TransThresholdPairCorrelation.ramanujanMode_eq_ramanujanLagCoefficient hm,
    TransThresholdPairCorrelation.ramanujanMode_eq_ramanujanLagCoefficient hL,
    ramanujanLagCoefficient_mul_eq g m hg hm n, coneFactor]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  push_cast
  rw [Real.sqrt_mul hg0.le, Real.sqrt_div htm.le, Real.sqrt_mul hg0.le]
  have h1 := Real.sqrt_pos.mpr htm
  have h2 := Real.sqrt_pos.mpr htL
  have h3 := Real.sqrt_pos.mpr hg0
  have h4 := Real.sqrt_pos.mpr hn0
  have ea : (m.totient : ℝ) = Real.sqrt m.totient * Real.sqrt m.totient :=
    (Real.mul_self_sqrt htm.le).symm
  have eb : (L.totient : ℝ) = Real.sqrt L.totient * Real.sqrt L.totient :=
    (Real.mul_self_sqrt htL.le).symm
  set a := Real.sqrt (m.totient : ℝ)
  set b := Real.sqrt (L.totient : ℝ)
  rw [ea, eb]
  field_simp
  rfl

/-- The top-stratum (coprime) energy `Σ_{(a,b)=1} W_{c,M}(a,b) y_a y_b`. -/
def topStratumEnergy (φ : ℝ → ℝ) (c : ℝ) (M : ℕ) (y : EuclideanSpace ℝ (PrimeHorizonIndex M)) : ℝ :=
  ∑ a : PrimeHorizonIndex M, ∑ b : PrimeHorizonIndex M,
    if Nat.Coprime (a : ℕ) b then completeWeilMatrix φ c M a b * y a * y b else 0

/-- The star pullback of a normalized Ramanujan packet is a lowered Ramanujan packet. -/
theorem starPull_normalizedRamanujanHorizonVector {g N e : ℕ} (hg : 0 < g) (he : 0 < e)
    (a : PrimeHorizonIndex (N / g)) :
    starPull g N (normalizedRamanujanHorizonVector e N) a =
      (Real.sqrt (Real.log N))⁻¹ * coneFactor g e *
        ramanujanHorizonVector (e / Nat.gcd e g) (N / g) a := by
  have ha := Finset.mem_Icc.mp a.2
  have hga : g * (a : ℕ) ∈ Icc 1 N := by
    refine Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hg.ne' (by omega)), ?_⟩
    calc g * (a : ℕ) ≤ g * (N / g) := Nat.mul_le_mul_left g ha.2
      _ ≤ N := Nat.mul_div_le N g
  simp only [starPull, primeHorizonExtension, dif_pos hga, normalizedRamanujanHorizonVector,
    ramanujanHorizonVector]
  change (Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile e (g * (a : ℕ)) = _
  rw [ramanujanPoleProfile_mul_eq hg he]
  ring

/-- **The cone expansion.** The energy of a graded piece is a `θ²`-weighted sum over the cone of
top-stratum energies of lowered conductors at the star resolutions. -/
theorem completeWeilEnergy_ramanujan_cone_expansion {φ : ℝ → ℝ} (hφ : EdgeHodgeTheory.Admissible φ)
    {c : ℝ} (hc : 0 < c) (N : ℕ) {e : ℕ} (he : 0 < e) :
    completeWeilEnergy φ c N (normalizedRamanujanHorizonVector e N) =
      (Real.log N)⁻¹ * ∑ g ∈ Icc 1 N, coneFactor g e ^ 2 *
        topStratumEnergy φ (starOverlap c N g) (N / g) (ramanujanHorizonVector (e / Nat.gcd e g) (N / g)) := by
  rw [completeWeilEnergy_gcd_stratification hφ hc N, mul_sum]
  refine sum_congr rfl fun g hg => ?_
  have hg0 : 0 < g := (Finset.mem_Icc.mp hg).1
  simp only [starPull_normalizedRamanujanHorizonVector hg0 he, topStratumEnergy, mul_sum]
  have hlog : (Real.sqrt (Real.log N))⁻¹ ^ 2 = (Real.log N)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  split_ifs
  · rw [← hlog]
    ring
  · simp

end GaloisForLFunctions.ArithmeticDegenerationTheory
