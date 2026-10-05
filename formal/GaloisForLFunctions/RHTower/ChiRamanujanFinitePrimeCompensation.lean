import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDivisorHaar
import GaloisForLFunctions.RHTower.WoldSieveNormalConeVonMangoldt
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Joint finite-prime and critical damping limit of the Ramanujan source

Compensation uses the same finite prime set at both damping parameters.
This proves a uniform logarithmic bound and convergence to von Mangoldt,
including the actual zero Fourier mode. No cubic cancellation is asserted.
-/

noncomputable section
open Filter Set ArithmeticFunction
open scoped BigOperators Topology
namespace RHTower.BAGTrace

/-- Prime incidences of the actual finite signed Ramanujan convolution. At zero,
every prime in the finite set acts; the zero frequency is not silently removed. -/
def ramanujanFiniteIncidence (P : Finset ℕ) (n : ℕ) : Finset ℕ :=
  P.filter (fun p => p.Prime ∧ p ∣ n)

/-- Literal Fourier multiplier of the finite convolution of delta minus damped
uniform prime-torsion measure. -/
def ramanujanFiniteMultiplier (P : Finset ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  woldSieveNormalFactor (ramanujanFiniteIncidence P n) ε

/-- Subtract at the same finite prime set before dividing by damping. -/
def ramanujanCompensatedMultiplier (P : Finset ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  (ramanujanFiniteMultiplier P ε n - ramanujanFiniteMultiplier P 0 n) / ε

private theorem normal_atom_bounds {p : ℕ} (hp : p.Prime) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ 1-Real.exp (-ε*Real.log p) ∧ 1-Real.exp (-ε*Real.log p) ≤ 1 ∧
      1-Real.exp (-ε*Real.log p) ≤ ε*Real.log p := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hl := Real.log_nonneg hp1
  have he : Real.exp (-ε*Real.log p) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have ht := Real.add_one_le_exp (-ε*Real.log p)
  exact ⟨by linarith, by linarith [Real.exp_pos (-ε*Real.log p)], by nlinarith⟩

private theorem normal_factor_nonneg {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ woldSieveNormalFactor S ε :=
  Finset.prod_nonneg (fun p hp => (normal_atom_bounds (hS p hp) hε).1)

private theorem normal_factor_le_atom {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) {ε : ℝ} (hε : 0 ≤ ε) {p : ℕ} (hp : p ∈ S) :
    woldSieveNormalFactor S ε ≤ 1-Real.exp (-ε*Real.log p) := by
  have h := Finset.prod_le_prod_of_subset_of_le_one
    (f := fun q : ℕ => 1-Real.exp (-ε*Real.log q))
    (Finset.singleton_subset_iff.mpr hp)
    (fun q hq => (normal_atom_bounds (hS q hq) hε).1)
    (fun q hq _ => (normal_atom_bounds (hS q hq) hε).2.1)
  simpa [woldSieveNormalFactor] using h

private theorem normal_factor_zero {S : Finset ℕ} (hS : S.Nonempty) :
    woldSieveNormalFactor S 0 = 0 := by
  simp only [woldSieveNormalFactor, neg_zero, zero_mul, Real.exp_zero, sub_self,
    Finset.prod_const]
  exact zero_pow (Finset.card_pos.mpr hS).ne'

private theorem finite_incidence_prime (P : Finset ℕ) (n : ℕ) :
    ∀ p ∈ ramanujanFiniteIncidence P n, p.Prime := by
  intro p hp
  exact (Finset.mem_filter.mp hp).2.1

/-- Uniform logarithmic bound, including primes not yet present in the finite net. -/
theorem ramanujanCompensatedMultiplier_bounds (P : Finset ℕ) {ε : ℝ}
    (hε : 0 < ε) {n : ℕ} (hn : 0 < n) :
    0 ≤ ramanujanCompensatedMultiplier P ε n ∧
      ramanujanCompensatedMultiplier P ε n ≤ Real.log n := by
  let S := ramanujanFiniteIncidence P n
  by_cases hS : S.Nonempty
  · obtain ⟨p,hp⟩ := hS
    have hprime := finite_incidence_prime P n p hp
    have hpn : p ∣ n := (Finset.mem_filter.mp hp).2.2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpn' : (p : ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd hn hpn
    have h0 : ramanujanFiniteMultiplier P 0 n = 0 := normal_factor_zero ⟨p,hp⟩
    rw [ramanujanCompensatedMultiplier,h0,sub_zero]
    refine ⟨div_nonneg (normal_factor_nonneg (finite_incidence_prime P n) hε.le) hε.le,?_⟩
    apply (div_le_iff₀ hε).mpr
    calc
      ramanujanFiniteMultiplier P ε n ≤ 1-Real.exp (-ε*Real.log p) :=
        normal_factor_le_atom (finite_incidence_prime P n) hε.le hp
      _ ≤ ε*Real.log p := (normal_atom_bounds hprime hε.le).2.2
      _ ≤ Real.log n*ε := by
        nlinarith [Real.log_le_log hp0 hpn']
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hzero : ramanujanCompensatedMultiplier P ε n = 0 := by
      simp [ramanujanCompensatedMultiplier,ramanujanFiniteMultiplier,
        show ramanujanFiniteIncidence P n = ∅ from he,woldSieveNormalFactor]
    rw [hzero]
    exact ⟨le_rfl,Real.log_nonneg (by exact_mod_cast hn)⟩

/-- A second prime kills the zero-frequency derivative uniformly over all later prime sets. -/
theorem ramanujanCompensatedMultiplier_zero_bound {P : Finset ℕ}
    (h2 : 2 ∈ P) (h3 : 3 ∈ P) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ ramanujanCompensatedMultiplier P ε 0 ∧
      ramanujanCompensatedMultiplier P ε 0 ≤ ε*Real.log 2*Real.log 3 := by
  let S := ramanujanFiniteIncidence P 0
  have h2S : 2 ∈ S := by simp [S,ramanujanFiniteIncidence,h2,Nat.prime_two]
  have h3S : 3 ∈ S := by simp [S,ramanujanFiniteIncidence,h3,Nat.prime_three]
  have hsub : ({2,3} : Finset ℕ) ⊆ S := by simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]; exact ⟨h2S,h3S⟩
  have h0 : ramanujanFiniteMultiplier P 0 0 = 0 := normal_factor_zero ⟨2,h2S⟩
  have hprod := Finset.prod_le_prod_of_subset_of_le_one
    (f := fun q : ℕ => 1-Real.exp (-ε*Real.log q)) hsub
    (fun q hq => (normal_atom_bounds (finite_incidence_prime P 0 q hq) hε.le).1)
    (fun q hq _ => (normal_atom_bounds (finite_incidence_prime P 0 q hq) hε.le).2.1)
  have h23 : ramanujanFiniteMultiplier P ε 0 ≤
      (1-Real.exp (-ε*Real.log 2))*(1-Real.exp (-ε*Real.log 3)) := by
    simpa [ramanujanFiniteMultiplier,woldSieveNormalFactor,S] using hprod
  rw [ramanujanCompensatedMultiplier,h0,sub_zero]
  refine ⟨div_nonneg (normal_factor_nonneg (finite_incidence_prime P 0) hε.le) hε.le,?_⟩
  apply (div_le_iff₀ hε).mpr
  have htwo := normal_atom_bounds Nat.prime_two hε.le
  have hthree := normal_atom_bounds Nat.prime_three hε.le
  have hh := mul_le_mul htwo.2.2 hthree.2.2 hthree.1
    (by positivity : 0 ≤ ε*Real.log 2)
  norm_num only [Nat.cast_ofNat] at hh
  exact h23.trans (hh.trans_eq (by ring))

theorem ramanujanFiniteIncidence_eq {P : Finset ℕ} {n : ℕ}
    (hn : n ≠ 0) (hP : n.primeFactors ⊆ P) :
    ramanujanFiniteIncidence P n = n.primeFactors := by
  ext p
  simp only [ramanujanFiniteIncidence,Finset.mem_filter]
  constructor
  · intro h
    exact Nat.mem_primeFactors.mpr ⟨h.2.1,h.2.2,hn⟩
  · intro h
    exact ⟨hP h,(Nat.mem_primeFactors.mp h).1,(Nat.mem_primeFactors.mp h).2.1⟩

/-- The finite-prime Fourier source is exactly the original divisor source once
all prime divisors of the coordinate have entered the net. -/
theorem ramanujanFiniteMultiplier_eq_divisorCoeff {P : Finset ℕ} {n : ℕ}
    (hn : n ≠ 0) (hP : n.primeFactors ⊆ P) (ε : ℝ) :
    ramanujanFiniteMultiplier P ε n = pmPowerDampedDivisorCoeff ε n := by
  rw [ramanujanFiniteMultiplier,ramanujanFiniteIncidence_eq hn hP,
    woldSieveNormalFactor,pmPowerDampedDivisorCoeff_eq_prod ε hn]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Real.rpow_def_of_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)]
  congr 2
  ring

/-- Joint finite-prime/damping convergence; no relation between the two limits is imposed. -/
theorem tendsto_ramanujanCompensatedMultiplier (n : ℕ) :
    Tendsto (fun z : Finset ℕ × ℝ => ramanujanCompensatedMultiplier z.1 z.2 n)
      (atTop ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (vonMangoldt n)) := by
  by_cases hn : n = 0
  · subst n
    have he : Tendsto (fun z : Finset ℕ × ℝ => z.2)
        (atTop ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_snd.mono_right nhdsWithin_le_nhds
    have hu := (he.mul_const (Real.log 2)).mul_const (Real.log 3)
    simp only [zero_mul] at hu
    have hP : ∀ᶠ z : Finset ℕ × ℝ in atTop ×ˢ 𝓝[>] (0 : ℝ),
        ({2,3} : Finset ℕ) ⊆ z.1 :=
      tendsto_fst.eventually (eventually_ge_atTop {2,3})
    have hp : ∀ᶠ z : Finset ℕ × ℝ in atTop ×ˢ 𝓝[>] (0 : ℝ), 0 < z.2 :=
      tendsto_snd.eventually self_mem_nhdsWithin
    have hb := hP.and hp
    have hb0 : ∀ᶠ z : Finset ℕ × ℝ in atTop ×ˢ 𝓝[>] (0 : ℝ),
        0 ≤ ramanujanCompensatedMultiplier z.1 z.2 0 := by
      filter_upwards [hb] with z hz
      exact (ramanujanCompensatedMultiplier_zero_bound
        (hz.1 (by simp)) (hz.1 (by simp)) hz.2).1
    have hb1 : ∀ᶠ z : Finset ℕ × ℝ in atTop ×ˢ 𝓝[>] (0 : ℝ),
        ramanujanCompensatedMultiplier z.1 z.2 0 ≤ z.2*Real.log 2*Real.log 3 := by
      filter_upwards [hb] with z hz
      exact (ramanujanCompensatedMultiplier_zero_bound
        (hz.1 (by simp)) (hz.1 (by simp)) hz.2).2
    simpa only [ArithmeticFunction.map_zero] using squeeze_zero' hb0 hb1 hu
  · have hd := (hasDerivAt_woldIncidenceNormalFactor n).tendsto_slope_zero_right
    have ht := hd.comp (tendsto_snd :
      Tendsto (fun z : Finset ℕ × ℝ => z.2) (atTop ×ˢ 𝓝[>] (0 : ℝ)) (𝓝[>] 0))
    apply ht.congr'
    filter_upwards [tendsto_fst.eventually (eventually_ge_atTop n.primeFactors)] with z hz
    simp only [Function.comp_apply,zero_add,smul_eq_mul]
    rw [ramanujanCompensatedMultiplier,ramanujanFiniteMultiplier,
      ramanujanFiniteMultiplier,ramanujanFiniteIncidence_eq hn hz]
    change z.2⁻¹ * (woldSieveNormalFactor n.primeFactors z.2 -
      woldSieveNormalFactor n.primeFactors 0) = _
    ring

/-- A single polynomial envelope for every integer frequency, including zero. -/
theorem ramanujanCompensatedMultiplier_nat_bound {P : Finset ℕ}
    (h2 : 2 ∈ P) (h3 : 3 ∈ P) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (n : ℕ) :
    0 ≤ ramanujanCompensatedMultiplier P ε n ∧
      ramanujanCompensatedMultiplier P ε n ≤ 6 * (1 + (n : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨h0, hb⟩ := ramanujanCompensatedMultiplier_zero_bound h2 h3 hε
    refine ⟨h0, hb.trans ?_⟩
    have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hl3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    have hm : ε * Real.log 2 ≤ 1 := by
      nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
    have hm3 := mul_le_mul hm hl3
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)) (by norm_num : (0 : ℝ) ≤ 1)
    norm_num only [Nat.cast_zero, add_zero, mul_one, one_mul] at hm3 ⊢
    linarith
  · obtain ⟨h0, hb⟩ := ramanujanCompensatedMultiplier_bounds P hε hn
    refine ⟨h0, hb.trans ?_⟩
    have hl := Real.log_le_sub_one_of_pos (by exact_mod_cast hn : (0 : ℝ) < n)
    linarith [Nat.cast_nonneg (α := ℝ) n]

end RHTower.BAGTrace
