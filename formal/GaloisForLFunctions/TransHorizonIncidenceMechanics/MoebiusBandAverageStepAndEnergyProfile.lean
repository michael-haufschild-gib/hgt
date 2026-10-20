import GaloisForLFunctions.TransHorizonIncidenceMechanics.MoebiusBuchstabStepSmoothCoreLaw
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DownwardBuchstabL2TelescopeAndSawtoothCoupling
import GaloisForLFunctions.BezoutValuationIncidence.CofinalMobiusQuadraticQuotientProfile
import GaloisForLFunctions.RHTower.FixedCoreSquarefreeDensity

/-!
# Band averages of Möbius horizon steps and the energy profile

By the smooth-core law the Möbius band step `Δ(m, B)` at a squarefree horizon `m ≥ 2` is a function
`v_B(r)` of the core `r = gcd(m, B#)` alone (`v_B(1) = B - 2`, `v_B(r) = Δ(r, B)` for `r > 1`), and
vanishes at non-squarefree horizons. The horizons of core `r` are `r m'` with `m'` squarefree and
free of primes `≤ B`, a set of density `δ_B / r`, `δ_B = (6/π²) ∏_{p ≤ B} p/(p+1)`. Hence the mean
step of band `B` exists and is the finite class average

`A(B) = lim_X (1/X) Σ_{2 ≤ m ≤ X} Δ(m, B) = δ_B Σ_{r | B#} v_B(r)/r`.

Telescoping the horizon from the top value `E_M(M; μ) = 1` down to `N`, the horizons
`m ∈ (M/(b+1), M/b]` all lie in band `b`, so at `M = (B+1)N`

`E_N((B+1)N; μ)/N → -(B+1) Σ_{b=1}^{B} A(b)/(b(b+1))`.

Comparing with the quotient-profile limit of the same energy gives the exact identity
`P(B) = -(B+1) Σ_{b ≤ B} A(b)/(b(b+1))` for the Möbius energy profile `P`, equivalently
`A(B) = (B+1) P(B-1) - B P(B)`: the mean horizon step of each band is a second difference of the
energy profile. For `B = 1, 2` the classes give `A(1) = -6/π²`, `A(2) = -4/π²` and `P(2) = 11/π²`.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Core classes -/

/-- The step value of the core class `r` in band `B`: `B - 2` for `r = 1`, `Δ(r, B)` otherwise. -/
def bandClassValue (B r : ℕ) : ℝ :=
  if r = 1 then (B : ℝ) - 2 else moebiusBandStep r B

/-- The density `δ_B = (6/π²) ∏_{p ≤ B} p/(p+1)` of squarefree integers free of primes `≤ B`. -/
def bandRoughDensity (B : ℕ) : ℝ :=
  RHTower.Sieve.squarefreeDensity * ∏ p ∈ (primorial B).primeFactors, (p : ℝ) / (p + 1)

/-- The mean Möbius step of band `B`: `A(B) = δ_B Σ_{r | B#} v_B(r)/r`. -/
def bandAverageStep (B : ℕ) : ℝ :=
  ∑ r ∈ (primorial B).divisors, bandClassValue B r * (bandRoughDensity B / r)

/-- Horizons `m ≤ X` in the core class `r` of band `B`. -/
def bandCoreCount (B r X : ℕ) : ℕ :=
  ((Icc 1 X).filter (fun m => Squarefree m ∧ Nat.gcd m (primorial B) = r)).card

/-- Every horizon `m ≥ 2` reads its step from its core class. -/
theorem moebiusBandStep_eq_sum_classes {m B : ℕ} (hm : 2 ≤ m) (hB : 1 ≤ B) :
    moebiusBandStep m B = ∑ r ∈ (primorial B).divisors,
      if Squarefree m ∧ Nat.gcd m (primorial B) = r then bandClassValue B r else 0 := by
  by_cases hsq : Squarefree m
  · simp only [hsq, true_and]
    rw [sum_ite_eq (primorial B).divisors (Nat.gcd m (primorial B)),
      if_pos (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, (primorial_pos B).ne'⟩),
      moebiusBandStep_eq_smoothCore hm hB hsq, bandClassValue]
  · simp only [hsq, false_and, if_false, sum_const_zero]
    simp [moebiusBandStep, moebiusReal_eq_zero_of_not_squarefree m hsq]

/-- A squarefree integer whose prime factors avoid the primes `≤ B` is coprime to `B#`. -/
private theorem coprime_primorial_of_disjoint {n B : ℕ} (hn : n ≠ 0)
    (hd : Disjoint n.primeFactors (primorial B).primeFactors) : Nat.Coprime n (primorial B) :=
  Nat.coprime_of_dvd fun _p hp hpn hpB => disjoint_left.mp hd
    (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩)
    (Nat.mem_primeFactors.mpr ⟨hp, hpB, (primorial_pos B).ne'⟩)

/-- The core class `r` of band `B` is `r` times the squarefree integers free of primes `≤ B`. -/
theorem bandCoreCount_eq {B r : ℕ} (hr : r ∈ (primorial B).divisors) (X : ℕ) :
    bandCoreCount B r X =
      RHTower.fixedCoreSquarefreeCount (primorial B).primeFactors (X / r) := by
  obtain ⟨hrB, -⟩ := Nat.mem_divisors.mp hr
  have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hrB (primorial_pos B)
  have hrsq : Squarefree r := (squarefree_primorial B).squarefree_of_dvd hrB
  unfold bandCoreCount RHTower.fixedCoreSquarefreeCount RHTower.fixedCoreSquarefreeIndices
  refine card_nbij' (· / r) (r * ·) ?_ ?_ ?_ ?_
  · intro m hm
    simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at hm ⊢
    obtain ⟨⟨hm1, hmX⟩, hsq, hg⟩ := hm
    have hrm : r ∣ m := hg ▸ Nat.gcd_dvd_left m _
    have hmr : r * (m / r) = m := Nat.mul_div_cancel' hrm
    have hsq' : Squarefree (r * (m / r)) := by rwa [hmr]
    have hcop : Nat.Coprime r (m / r) := Nat.coprime_of_squarefree_mul hsq'
    refine ⟨⟨Nat.div_pos (Nat.le_of_dvd (by omega) hrm) hr0, Nat.div_le_div_right hmX⟩,
      hsq'.of_mul_right, disjoint_left.mpr fun p hpm hpB => ?_⟩
    obtain ⟨hp, hpd, -⟩ := Nat.mem_primeFactors.mp hpm
    have hpr : p ∣ r := hg ▸ Nat.dvd_gcd (hpd.trans (Nat.div_dvd_of_dvd hrm))
      (Nat.mem_primeFactors.mp hpB).2.1
    exact hp.one_lt.ne' ((hcop.coprime_dvd_left hpr).eq_one_of_dvd hpd)
  · intro n hn
    simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at hn ⊢
    obtain ⟨⟨hn1, hnX⟩, hnsq, hd⟩ := hn
    have hnB := coprime_primorial_of_disjoint (by omega) hd
    have hrn : Nat.Coprime r n := hnB.symm.coprime_dvd_left hrB
    refine ⟨⟨Nat.mul_pos hr0 (by omega), by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hr0).mp hnX⟩,
      Nat.squarefree_mul_iff.mpr ⟨hrn, hrsq, hnsq⟩, ?_⟩
    conv_lhs => rw [← Nat.mul_div_cancel' hrB]
    rw [Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one (hnB.coprime_dvd_right (Nat.div_dvd_of_dvd hrB)),
      mul_one]
  · intro m hm
    simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at hm
    exact Nat.mul_div_cancel' (hm.2.2 ▸ Nat.gcd_dvd_left m _)
  · intro n _
    exact Nat.mul_div_cancel_left n hr0

/-- **Class-count formula.** `Σ_{2 ≤ m ≤ X} Δ(m, B) = Σ_{r | B#} v_B(r) (#class r up to X − [r = 1])`. -/
theorem sum_moebiusBandStep_eq_classes {B X : ℕ} (hB : 1 ≤ B) (hX : 1 ≤ X) :
    ∑ m ∈ Ioc 1 X, moebiusBandStep m B = ∑ r ∈ (primorial B).divisors,
      bandClassValue B r * ((bandCoreCount B r X : ℝ) - if r = 1 then 1 else 0) := by
  rw [sum_congr rfl fun m hm => moebiusBandStep_eq_sum_classes
    (by simp only [mem_Ioc] at hm; omega) hB, sum_comm]
  refine sum_congr rfl fun r _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  have hI : Icc 1 X = insert 1 (Ioc 1 X) := by
    ext m; simp only [mem_Icc, mem_insert, mem_Ioc]; omega
  unfold bandCoreCount
  rw [hI, filter_insert]
  by_cases hr1 : r = 1
  · subst hr1
    rw [if_pos ⟨squarefree_one, Nat.gcd_one_left _⟩, card_insert_of_notMem (by simp), if_pos rfl]
    push_cast; ring
  · rw [if_neg (show ¬ (Squarefree 1 ∧ Nat.gcd 1 (primorial B) = r) from
      fun h => hr1 (by rw [← h.2, Nat.gcd_one_left])), if_neg hr1, sub_zero]

/-! ### The band-average law -/

/-- `⌊kN/r⌋ / N → k/r`. -/
theorem tendsto_natDiv_mul_div (k : ℕ) {r : ℕ} (hr : 0 < r) :
    Tendsto (fun N : ℕ => ((k * N / r : ℕ) : ℝ) / N) atTop (𝓝 ((k : ℝ) / r)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hlow : Tendsto (fun N : ℕ => (k : ℝ) / r - 1 / N) atTop (𝓝 ((k : ℝ) / r)) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat).const_sub ((k : ℝ) / r)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have h := Nat.lt_div_mul_add (a := k * N) hr
    have h' : (k : ℝ) * N < ((k * N / r : ℕ) : ℝ) * r + r := by exact_mod_cast h
    have key : (k : ℝ) / r ≤ (((k * N / r : ℕ) : ℝ) + 1) / N := by
      rw [div_le_div_iff₀ hrR hNR]; nlinarith
    rw [add_div] at key
    linarith
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_div_iff₀ hNR hrR]
    have := Nat.cast_div_le (α := ℝ) (m := k * N) (n := r)
    rw [le_div_iff₀ hrR] at this
    push_cast at this; linarith

/-- **Band-average law.** In every band `B ≥ 1` the mean Möbius horizon step exists and equals
the finite class average: `(1/X) Σ_{2 ≤ m ≤ X} Δ(m, B) → A(B)`. -/
theorem tendsto_sum_moebiusBandStep_div {B : ℕ} (hB : 1 ≤ B) :
    Tendsto (fun X : ℕ => (∑ m ∈ Ioc 1 X, moebiusBandStep m B) / X) atTop
      (𝓝 (bandAverageStep B)) := by
  have hcls : ∀ r ∈ (primorial B).divisors, Tendsto (fun X : ℕ =>
      bandClassValue B r * (((bandCoreCount B r X : ℝ) - if r = 1 then 1 else 0) / X))
      atTop (𝓝 (bandClassValue B r * (bandRoughDensity B / r))) := by
    intro r hr
    have hr0 : 0 < r := Nat.pos_of_mem_divisors hr
    have hP : ∀ p ∈ (primorial B).primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
    have hc := (RHTower.tendsto_fixedCoreSquarefreeCount_div _ hP).comp
      (Nat.tendsto_div_const_atTop hr0.ne')
    have hq := tendsto_natDiv_mul_div 1 hr0
    simp only [one_mul, Nat.cast_one] at hq
    have hprod := hc.mul hq
    have hsub := hprod.sub ((tendsto_one_div_atTop_nhds_zero_nat).const_mul
      (if r = 1 then (1 : ℝ) else 0))
    rw [mul_zero, sub_zero] at hsub
    have hval : bandRoughDensity B / r = (RHTower.Sieve.squarefreeDensity *
        ∏ p ∈ (primorial B).primeFactors, (p : ℝ) / (p + 1)) * (1 / r) := by
      rw [bandRoughDensity, mul_one_div]
    have h := hsub.const_mul (bandClassValue B r)
    rw [← hval] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop r] with X hX
    have hXr : 0 < X / r := Nat.div_pos hX hr0
    have hXrR : (0 : ℝ) < (X / r : ℕ) := by exact_mod_cast hXr
    have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    simp only [Function.comp_apply]
    rw [bandCoreCount_eq hr]
    field_simp
  have hsum := tendsto_finsetSum _ hcls
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [sum_moebiusBandStep_eq_classes hB hX, sum_div]
  exact sum_congr rfl fun r _ => by ring

/-! ### Telescoping across bands -/

/-- The Möbius prefix energy is `1` minus the horizon steps between `N ≥ 1` and `M`. -/
theorem sieveL2PrefixEnergy_moebius_eq_one_sub_bandSteps {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    sieveL2PrefixEnergy N M moebiusReal = 1 - ∑ m ∈ Ioc N M, moebiusBandStep m (M / m) := by
  rw [sieveL2PrefixEnergy_moebiusReal_eq_one_sub_sum_Ico (by omega) hNM]
  congr 1
  rw [sum_filter]
  have hshift : ∑ m ∈ Ioc N M, moebiusBandStep m (M / m) =
      ∑ n ∈ Ico N M, moebiusBandStep (n + 1) (M / (n + 1)) := by
    refine sum_nbij' (· - 1) (· + 1) ?_ ?_ ?_ ?_ ?_
    · intro x hx; simp only [mem_Ioc, mem_Ico] at hx ⊢; omega
    · intro x hx; simp only [mem_Ioc, mem_Ico] at hx ⊢; omega
    · intro x hx; simp only [mem_Ioc] at hx; omega
    · intro x _; omega
    · intro x hx; simp only [mem_Ioc] at hx; rw [Nat.sub_add_cancel (by omega)]
  rw [hshift]
  refine sum_congr rfl fun n _ => ?_
  split_ifs with hsq
  · exact sieveL2PrefixEnergy_moebius_step_eq_bandStep n M
  · simp [moebiusBandStep, moebiusReal_eq_zero_of_not_squarefree _ hsq]

/-- Horizons `m ∈ (M/(b+1), M/b]` lie in band `b`: the trans-horizon range `(M/(K+1), M]` splits
into the bands `b = 1, …, K`. -/
theorem sum_Ioc_band_split (M : ℕ) (g : ℕ → ℕ → ℝ) {K : ℕ} (hK : 1 ≤ K) :
    ∑ m ∈ Ioc (M / (K + 1)) M, g m (M / m) =
      ∑ b ∈ Icc 1 K, ∑ m ∈ Ioc (M / (b + 1)) (M / b), g m b := by
  have hband : ∀ b, 1 ≤ b → ∑ m ∈ Ioc (M / (b + 1)) (M / b), g m (M / m) =
      ∑ m ∈ Ioc (M / (b + 1)) (M / b), g m b := fun b hb =>
    sum_congr rfl fun m hm => by
      simp only [mem_Ioc] at hm
      have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hm.1
      have h1 : M / m < b + 1 := (Nat.div_lt_iff_lt_mul hm0).mpr
        (by rw [mul_comm]; exact (Nat.div_lt_iff_lt_mul (by omega)).mp hm.1)
      have h2 : b ≤ M / m := (Nat.le_div_iff_mul_le hm0).mpr
        (by rw [mul_comm]; exact (Nat.le_div_iff_mul_le (by omega)).mp hm.2)
      rw [show M / m = b by omega]
  induction K, hK using Nat.le_induction with
  | base => rw [Icc_self, sum_singleton, ← hband 1 le_rfl, Nat.div_one]
  | succ K hK ih =>
    rw [← sum_Ioc_consecutive _ (Nat.div_le_div_left (by omega) (by omega))
      (Nat.div_le_self M (K + 1)), ih, hband (K + 1) (by omega), sum_Icc_succ_top (by omega),
      add_comm]

/-- **Band representation of the energy.** For `M = (B+1)N`, `N ≥ 1`:
`E_N(M; μ) = 1 - Σ_{b=1}^{B} (S_b(M/b) - S_b(M/(b+1)))`, `S_b(X) = Σ_{2 ≤ m ≤ X} Δ(m, b)`. -/
theorem sieveL2PrefixEnergy_moebius_linear_horizon_eq_bands {B N : ℕ} (hB : 1 ≤ B) (hN : 1 ≤ N) :
    sieveL2PrefixEnergy N ((B + 1) * N) moebiusReal = 1 - ∑ b ∈ Icc 1 B,
      ((∑ m ∈ Ioc 1 ((B + 1) * N / b), moebiusBandStep m b) -
        ∑ m ∈ Ioc 1 ((B + 1) * N / (b + 1)), moebiusBandStep m b) := by
  set M := (B + 1) * N
  have hMN : M / (B + 1) = N := Nat.mul_div_cancel_left N (by omega)
  have hsplit := sum_Ioc_band_split M (fun m b => moebiusBandStep m b) hB
  rw [hMN] at hsplit
  rw [sieveL2PrefixEnergy_moebius_eq_one_sub_bandSteps hN (Nat.le_mul_of_pos_left N (by omega)),
    hsplit]
  congr 1
  refine sum_congr rfl fun b hb => ?_
  obtain ⟨hb1, hbB⟩ := mem_Icc.mp hb
  have hM : b + 1 ≤ M := by simp only [M]; nlinarith
  have hlo : 1 ≤ M / (b + 1) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  rw [eq_sub_iff_add_eq, add_comm, sum_Ioc_consecutive _ hlo
    (Nat.div_le_div_left (by omega) (by omega))]

/-- **Band integral of the energy profile.**
`E_N((B+1)N; μ)/N → -(B+1) Σ_{b=1}^{B} A(b) (1/b - 1/(b+1))`. -/
theorem tendsto_sieveL2PrefixEnergy_moebius_linear_horizon_bands {B : ℕ} (hB : 1 ≤ B) :
    Tendsto (fun N : ℕ => sieveL2PrefixEnergy N ((B + 1) * N) moebiusReal / N) atTop
      (𝓝 (-∑ b ∈ Icc 1 B, bandAverageStep b *
        (((B + 1 : ℕ) : ℝ) / b - ((B + 1 : ℕ) : ℝ) / (b + 1 : ℕ)))) := by
  -- each partial band sum, read at `kN/r`, has slope `A(b) k/r`
  have hpart : ∀ b, 1 ≤ b → ∀ r, 0 < r → Tendsto (fun N : ℕ =>
      (∑ m ∈ Ioc 1 ((B + 1) * N / r), moebiusBandStep m b) / N) atTop
      (𝓝 (bandAverageStep b * (((B + 1 : ℕ) : ℝ) / r))) := by
    intro b hb r hr
    have hX : Tendsto (fun N : ℕ => (B + 1) * N / r) atTop atTop :=
      (Nat.tendsto_div_const_atTop hr.ne').comp
        (tendsto_id.const_mul_atTop' (by omega : 0 < B + 1))
    have h1 := ((tendsto_sum_moebiusBandStep_div hb).comp hX).mul (tendsto_natDiv_mul_div (B + 1) hr)
    refine h1.congr' ?_
    filter_upwards [hX.eventually (eventually_gt_atTop 0), eventually_gt_atTop 0] with N hXN hN
    have h1R : (0 : ℝ) < ((B + 1) * N / r : ℕ) := by exact_mod_cast hXN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [Function.comp_apply]
    field_simp
  have hbands := tendsto_finsetSum (Icc 1 B) fun b hb =>
    (hpart b (mem_Icc.mp hb).1 b (by have := (mem_Icc.mp hb).1; omega)).sub
      (hpart b (mem_Icc.mp hb).1 (b + 1) (by omega))
  have hlim := (tendsto_one_div_atTop_nhds_zero_nat).sub hbands
  have heq : (0 : ℝ) - ∑ b ∈ Icc 1 B, (bandAverageStep b * (((B + 1 : ℕ) : ℝ) / b) -
      bandAverageStep b * (((B + 1 : ℕ) : ℝ) / (b + 1 : ℕ))) = -∑ b ∈ Icc 1 B, bandAverageStep b *
        (((B + 1 : ℕ) : ℝ) / b - ((B + 1 : ℕ) : ℝ) / (b + 1 : ℕ)) := by
    rw [zero_sub]; congr 1; exact sum_congr rfl fun b _ => by ring
  rw [heq] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [sieveL2PrefixEnergy_moebius_linear_horizon_eq_bands hB hN, sub_div, sum_div]
  congr 1
  exact sum_congr rfl fun b _ => (sub_div _ _ _).symm

/-! ### The profile identity -/

/-- **Profile identity.** The Möbius energy profile is the band integral of the mean steps:
`P(B) = -(B+1) Σ_{b=1}^{B} A(b)/(b(b+1))`. -/
theorem cofinalMobiusQuadraticProfile_eq_band_integral {B : ℕ} (hB : 1 ≤ B) :
    cofinalMobiusQuadraticProfile B = -((B : ℝ) + 1) *
      ∑ b ∈ Icc 1 B, bandAverageStep b / ((b : ℝ) * (b + 1)) := by
  have h := tendsto_nhds_unique (tendsto_sieveL2PrefixEnergy_moebiusReal_linear_horizon B)
    (tendsto_sieveL2PrefixEnergy_moebius_linear_horizon_bands hB)
  rw [h, mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun b hb => ?_
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (mem_Icc.mp hb).1
  push_cast
  field_simp
  ring

/-- **Mean steps are second differences of the profile.** `A(B) = (B+1) P(B-1) - B P(B)`. -/
theorem bandAverageStep_eq_profile {B : ℕ} (hB : 1 ≤ B) :
    bandAverageStep B =
      ((B : ℝ) + 1) * cofinalMobiusQuadraticProfile (B - 1) - B * cofinalMobiusQuadraticProfile B := by
  obtain ⟨C, rfl⟩ : ∃ C, B = C + 1 := ⟨B - 1, by omega⟩
  rw [Nat.add_sub_cancel, cofinalMobiusQuadraticProfile_eq_band_integral hB, sum_Icc_succ_top hB]
  rcases Nat.eq_zero_or_pos C with rfl | hC
  · simp [cofinalMobiusQuadraticProfile_zero]
    field_simp
    ring
  · rw [cofinalMobiusQuadraticProfile_eq_band_integral hC]
    push_cast
    have h1 : (0 : ℝ) < C + 1 := by positivity
    field_simp
    ring

/-! ### The first two bands -/

/-- `A(1) = -6/π²`: in the first band every squarefree horizon steps by `-1`. -/
theorem bandAverageStep_one : bandAverageStep 1 = -RHTower.Sieve.squarefreeDensity := by
  have hp : primorial 1 = 1 := by decide
  simp [bandAverageStep, bandRoughDensity, bandClassValue, hp]
  norm_num

/-- `A(2) = -4/π²`: odd squarefree horizons step by `0`, even ones by `-2`. -/
theorem bandAverageStep_two :
    bandAverageStep 2 = -(2 / 3) * RHTower.Sieve.squarefreeDensity := by
  have hp : primorial 2 = 2 := by decide
  have hd : (2 : ℕ).divisors = {1, 2} := by decide
  have hpf : (2 : ℕ).primeFactors = {2} := Nat.prime_two.primeFactors
  rw [bandAverageStep, bandRoughDensity, hp, hd, hpf, sum_insert (by decide), sum_singleton,
    prod_singleton]
  simp only [bandClassValue, show (2 : ℕ) ≠ 1 by decide, if_false,
    moebiusBandStep_two]
  push_cast
  ring

/-- `P(2) = 11/π²`: `E_N(3N; μ)/N → (11/6) · 6/π²`. -/
theorem cofinalMobiusQuadraticProfile_two :
    cofinalMobiusQuadraticProfile 2 = 11 / 6 * RHTower.Sieve.squarefreeDensity := by
  have h := bandAverageStep_eq_profile (B := 2) (by norm_num)
  rw [bandAverageStep_two, show (2 : ℕ) - 1 = 1 from rfl, cofinalMobiusQuadraticProfile_one] at h
  push_cast at h
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
