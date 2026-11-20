import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFirstOmittedPrimePowerAtEveryCutoff
import GaloisForLFunctions.ArithmeticPositiveDuality.FractionalDiscrepancyOfAtomicRows
import GaloisForLFunctions.RHTower.Sieve.SmallestPart

/-!
# The center's radical at the first omitted root

At y = x^(1/(J+1)), the lost prime logarithms sum to log gcd(n, ⌊y⌋#).
This single integer accounts for all dependence on the center at the
first omitted scale. Primorial centers attain every fraction of the
leading coefficient and pay exactly the logarithmic mass they remove.
The complementary fractional discrepancy kernels of Meiners and Gnewuch,
§3.5, recover the entire clipped radical from the finite prime-divisor row.
-/

noncomputable section
open Finset Filter
open MeasureTheory GaloisForLFunctions.ArithmeticPositiveDuality.FractionalDiscrepancy
open scoped Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Squarefree part of the center supported on primes through y. -/
def clippedPrimeRadical (n : ℕ) (y : ℝ) := n.gcd (primorial ⌊y⌋₊)

/-- The exact loss from restricting the Chebyshev prime sum to primes
coprime to the center, including the zero center. -/
theorem log_clipped_prime_radical (n : ℕ) (y : ℝ) :
    Chebyshev.theta y - coprimeTheta n y = Real.log (clippedPrimeRadical n y) := by
  let G := clippedPrimeRadical n y
  have hs : Squarefree G := (squarefree_primorial ⌊y⌋₊).squarefree_of_dvd (Nat.gcd_dvd_right _ _)
  let S := (Ioc 0 ⌊y⌋₊).filter Nat.Prime
  have hset : G.primeFactors=S.filter (fun p => ¬n.Coprime p) := by
    ext p
    constructor
    · intro hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hdiv := Nat.dvd_of_mem_primeFactors hp
      obtain ⟨hd,hp'⟩ := Nat.dvd_gcd_iff.mp (show p ∣ n.gcd (primorial ⌊y⌋₊) from hdiv)
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨hprime.pos,hprime.dvd_primorial_iff.mp hp'⟩,hprime⟩,?_⟩
      exact fun h => (hprime.coprime_iff_not_dvd.mp h.symm) hd
    · intro hp
      obtain ⟨hm,hc⟩ := mem_filter.mp hp
      obtain ⟨hi,hp⟩ := mem_filter.mp hm
      have hd : p ∣ n := by by_contra h; exact hc (hp.coprime_iff_not_dvd.mpr h).symm
      exact Nat.mem_primeFactors.mpr ⟨hp,Nat.dvd_gcd hd (hp.dvd_primorial_iff.mpr (mem_Ioc.mp hi).2),hs.ne_zero⟩
  have he : Real.log (G:ℝ)=∑ p ∈ G.primeFactors, Real.log p := by
    conv_lhs => rw [←Nat.prod_primeFactors_of_squarefree hs,Nat.cast_prod]
    exact Real.log_prod fun p hp => Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  change _ = Real.log (G:ℝ)
  rw [he,hset,sum_filter]
  unfold Chebyshev.theta coprimeTheta
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  by_cases h : n.Coprime p
  · rw [if_pos h,if_neg (not_not_intro h),sub_self]
  · rw [if_neg h,if_pos h,sub_zero]

/-- Two translates of the complementary power kernel applied to one
prime-divisor field recover the log of the center's radical through y.
A prime exactly at the endpoint is included. -/
theorem fractional_reading_of_the_clipped_radical {n : ℕ} (hn : 0<n) {y : ℝ} (hy : 0≤y)
    {b : ℝ} (hb : b∈Set.Ioo (0:ℝ) 1) :
    (∫ t : ℝ, (cutPower (-b) t-cutPower (-b) (t-y)) *
      field n.primeFactors Nat.cast (fun p => Real.log p) (b-1) t) =
      ProbabilityTheory.beta (1-b) b * Real.log (clippedPrimeRadical n y) := by
  let G := clippedPrimeRadical n y
  have hs : Squarefree G := (squarefree_primorial ⌊y⌋₊).squarefree_of_dvd (Nat.gcd_dvd_right _ _)
  have hlog : Real.log (G:ℝ)=∑ p ∈ n.primeFactors.filter (fun p => p≤⌊y⌋₊), Real.log p := by
    rw [←_root_.RHTower.Sieve.primeFactors_gcd_primorial hn.ne']
    change Real.log (G:ℝ)=∑ p ∈ G.primeFactors, Real.log p
    conv_lhs => rw [←Nat.prod_primeFactors_of_squarefree hs,Nat.cast_prod]
    exact Real.log_prod fun p hp => Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  let w := fun p : ℕ => Real.log p
  have hi (z : ℝ) : Integrable (fun t => cutPower (-b) (t-z)*field n.primeFactors Nat.cast w (b-1) t) := by
    simpa only [show 1-b-1= -b by ring] using
      integrable_pairing n.primeFactors Nat.cast w (sub_pos.mpr hb.2) hb.1 z
  have hi₀ := hi 0
  have hv₀ := complementary_tail n.primeFactors Nat.cast w hb 0
  simp only [sub_zero] at hi₀ hv₀
  simp only [sub_mul]
  rw [integral_sub hi₀ (hi y),hv₀,complementary_tail n.primeFactors Nat.cast w hb y,←mul_sub]
  change _ = _ * Real.log (G:ℝ)
  rw [hlog,sum_filter,←sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro p hp
  rw [if_pos ((Nat.cast_pos (α:=ℝ)).mpr (Nat.prime_of_mem_primeFactors hp).pos)]
  by_cases h : (p:ℝ)≤y
  · rw [if_neg (not_lt.mpr h),if_pos (Nat.le_floor h),sub_zero]
  · rw [if_pos (lt_of_not_ge h),if_neg (fun h' => h ((Nat.le_floor_iff hy).mp h')),sub_self]

/-- Adding back the clipped radical gives the same leading coefficient
for every varying center, with no upper bound on its growth. -/
theorem radical_law_for_the_first_omitted_power {ι : Type*} {l : Filter ι} {J : ℕ} (hJ : 2≤J)
    (u : ι → ℝ) (hu : Tendsto u l atTop) (n : ι → ℕ) :
    let r := 1/((J:ℝ)+1)
    Tendsto (fun i => (remainingProperPowerPrice (n i) J (u i) +
      ((J:ℝ)+1)*Real.log (clippedPrimeRadical (n i) ((u i)^r)))/(u i)^r) l (𝓝 ((J:ℝ)+1)) := by
  let r := 1/((J:ℝ)+1)
  have hr : 0<r := by dsimp only [r]; positivity
  have hθ := (_root_.RHTower.tendsto_theta_div_self.comp ((tendsto_rpow_atTop hr).comp hu)).const_mul ((J:ℝ)+1)
  have ht := (normalized_omitted_row_error hJ u hu n).add hθ
  rw [mul_one,zero_add] at ht
  apply ht.congr
  intro i
  change (_-_*_)/(u i)^r + ((J:ℝ)+1)*(Chebyshev.theta ((u i)^r)/(u i)^r) = _
  rw [←log_clipped_prime_radical]
  ring

/-- Along any sequence the price converges after normalization exactly
when the clipped radical has the complementary normalized limit. -/
theorem omitted_power_limit_iff_radical_limit {ι : Type*} {l : Filter ι} {J : ℕ} (hJ : 2≤J)
    (u : ι → ℝ) (hu : Tendsto u l atTop) (n : ι → ℕ) (t : ℝ) :
    let r := 1/((J:ℝ)+1)
    Tendsto (fun i => remainingProperPowerPrice (n i) J (u i)/(u i)^r) l (𝓝 (((J:ℝ)+1)*(1-t))) ↔
      Tendsto (fun i => Real.log (clippedPrimeRadical (n i) ((u i)^r))/(u i)^r) l (𝓝 t) := by
  let K := (J:ℝ)+1
  let r := 1/K
  have hK : K ≠ 0 := by dsimp [K]; positivity
  have h := radical_law_for_the_first_omitted_power hJ u hu n
  constructor
  · intro hp
    have ht := (h.sub hp).div_const K
    change Tendsto _ _ (𝓝 ((K-K*(1-t))/K)) at ht
    rw [show (K-K*(1-t))/K=t by field_simp [hK]; ring] at ht
    apply ht.congr
    intro i
    change ((_+K*_)/(u i)^r-_/(u i)^r)/K=_
    rw [add_div,add_sub_cancel_left,mul_div_assoc,mul_div_cancel_left₀ _ hK]
  · intro hg
    have ht := h.sub (hg.const_mul K)
    change Tendsto _ _ (𝓝 (K-K*t)) at ht
    rw [show K-K*t=K*(1-t) by ring] at ht
    apply ht.congr
    intro i
    change (_+K*_)/(u i)^r-K*(_/(u i)^r)=_
    rw [add_div,mul_div_assoc,add_sub_cancel_right]

private theorem scaled_theta_limit {t : ℝ} (ht : 0≤t) :
    Tendsto (fun y : ℝ => Chebyshev.theta (t*y)/y) atTop (𝓝 t) := by
  rcases ht.eq_or_lt with he | hp
  · rw [←he]
    simpa [Chebyshev.theta] using (tendsto_const_nhds (x:=(0:ℝ)) (f:=atTop (α:=ℝ)))
  have h := (_root_.RHTower.tendsto_theta_div_self.comp (tendsto_id.const_mul_atTop hp)).mul_const t
  rw [one_mul] at h
  apply h.congr
  intro y
  change Chebyshev.theta (t*y)/(t*y)*t=_
  rw [mul_comm t y,←div_div,div_mul_cancel₀ _ hp.ne']

/-- Primorials realize the full loss interval. The logarithmic size of
the center, divided by the first omitted root, converges to exactly the
fraction removed from its prime row. -/
theorem every_omitted_power_fraction_at_its_exact_cost {J : ℕ} (hJ : 2≤J) {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) :
    let r := 1/((J:ℝ)+1)
    let n := fun x : ℝ => primorial ⌊t*x^r⌋₊
    Tendsto (fun x : ℝ => Real.log (n x)/x^r) atTop (𝓝 t) ∧
      Tendsto (fun x : ℝ => remainingProperPowerPrice (n x) J x/x^r) atTop (𝓝 (((J:ℝ)+1)*(1-t))) := by
  let r := 1/((J:ℝ)+1)
  let n := fun x : ℝ => primorial ⌊t*x^r⌋₊
  have hr : 0<r := by dsimp only [r]; positivity
  have hc : Tendsto (fun x : ℝ => Real.log (n x)/x^r) atTop (𝓝 t) := by
    apply ((scaled_theta_limit ht.1).comp (tendsto_rpow_atTop hr)).congr
    intro x
    exact congrArg (fun v : ℝ => v/x^r) (Chebyshev.theta_eq_log_primorial _)
  refine ⟨hc,(omitted_power_limit_iff_radical_limit hJ id tendsto_id n t).mpr ?_⟩
  apply hc.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  have hu := Nat.floor_mono (mul_le_of_le_one_left (Real.rpow_nonneg hx.le r) ht.2)
  have hd : n x ∣ primorial ⌊x^r⌋₊ := primorial_dvd_primorial hu
  change Real.log (n x)/x^r = Real.log ((n x).gcd (primorial ⌊x^r⌋₊))/x^r
  rw [Nat.gcd_eq_left hd]

/-- Among all positive varying centers suppressing a fraction t of the
first omitted coefficient, the least limiting logarithmic cost is t. -/
theorem least_cost_of_an_omitted_power_fraction {J : ℕ} (hJ : 2≤J) {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) :
    let r := 1/((J:ℝ)+1)
    IsLeast {s : ℝ | ∃ n : ℝ → ℕ, (∀ x, 0<n x) ∧
      Tendsto (fun x => Real.log (n x)/x^r) atTop (𝓝 s) ∧
      Tendsto (fun x => remainingProperPowerPrice (n x) J x/x^r) atTop (𝓝 (((J:ℝ)+1)*(1-t)))} t := by
  let r := 1/((J:ℝ)+1)
  have he := every_omitted_power_fraction_at_its_exact_cost hJ ht
  refine ⟨⟨fun x => primorial ⌊t*x^r⌋₊,fun _ => primorial_pos _,he.1,he.2⟩,?_⟩
  rintro s ⟨n,hn,hs,hp⟩
  have hg := (omitted_power_limit_iff_radical_limit hJ id tendsto_id n t).mp hp
  apply le_of_tendsto_of_tendsto hg hs
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  have hpos : 0<clippedPrimeRadical (n x) (x^r) := Nat.gcd_pos_of_pos_left _ (hn x)
  have hle : clippedPrimeRadical (n x) (x^r) ≤ n x := Nat.le_of_dvd (hn x) (Nat.gcd_dvd_left _ _)
  exact div_le_div_of_nonneg_right (Real.log_le_log (Nat.cast_pos.mpr hpos) (Nat.cast_le.mpr hle))
    (Real.rpow_nonneg hx.le _)

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
