import GaloisForLFunctions.RHTower.SoninSemilocalGradingBounds
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Geometric-scale profile of the one-prime semilocal grading coefficient

The one-prime Euler source is sampled on the discrete frequency lattice `M log p`.  On the
geometric degree subsequence `k_j = c p^(2j)`, a frequency with fixed offset `M = j + s`
has a nonzero scaling limit.  Positive and negative offsets admit independent geometric
majorants, so Tannery's theorem assembles their limits into an exact bilateral profile.

Unlike the earlier two-sided `k^(-3/4)` bounds, these theorems retain the prime-lattice phase and
the exact limiting exponential.  The full profile is invariant under `c ↦ c p^2`, and the
intrinsically normalized literal Jacobi coefficient converges to it.  The proofs use no
asymptotic hypothesis on the source.
-/

noncomputable section

open Complex Filter MeasureTheory Polynomial Real Set
open scoped BigOperators Topology

namespace RHTower

def routeJOnePrimeGeometricScale (c p j : ℕ) : ℕ :=
  c * p ^ (2 * j)

def routeJOnePrimeRawMagnitude (k p M : ℕ) : ℝ :=
  semilocalPrimePoissonRatio p ^ M *
    semilocalArchimedeanCharacteristic ((M : ℝ) * Real.log p) *
    Real.tanh ((M : ℝ) * Real.log p) ^ (2 * k)

theorem tendsto_routeJOnePrimeGeometricScale_atTop
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime) :
    Tendsto (routeJOnePrimeGeometricScale c p) atTop atTop := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpow : Tendsto (fun j : ℕ => (p : ℝ) ^ (2 * j)) atTop atTop := by
    simpa [pow_mul] using
      (tendsto_pow_atTop_atTop_of_one_lt
        (show (1 : ℝ) < p ^ 2 by nlinarith [sq_nonneg ((p : ℝ) - 1)]))
  have hmul := hpow.const_mul_atTop (show (0 : ℝ) < c by exact_mod_cast hc)
  have hcast :
      Tendsto (fun j => (routeJOnePrimeGeometricScale c p j : ℝ)) atTop atTop := by
    simpa [routeJOnePrimeGeometricScale] using hmul
  exact (tendsto_natCast_atTop_iff (R := ℝ)).mp hcast

theorem tendsto_routeJOnePrime_geometric_tanhPow
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime) (s : ℕ) :
    Tendsto
      (fun j =>
        Real.tanh (((j + s : ℕ) : ℝ) * Real.log p) ^
          (2 * routeJOnePrimeGeometricScale c p j))
      atTop
      (𝓝 (Real.exp (-4 * (c : ℝ) / (p : ℝ) ^ (2 * s)))) := by
  let A : ℝ := (p : ℝ) ^ (2 * s)
  let g : ℕ → ℝ := fun n => -(2 * (c : ℝ)) / (A * n + c)
  have hA : 0 < A := by
    dsimp [A]
    exact pow_pos (by exact_mod_cast hp.pos) _
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hfrac :
      Tendsto (fun n : ℕ => -(2 * (c : ℝ)) / (A + (c : ℝ) / n))
        atTop (𝓝 (-(2 * (c : ℝ)) / A)) := by
    have hden :
        Tendsto (fun n : ℕ => A + (c : ℝ) / n)
          atTop (𝓝 (A + 0)) :=
      tendsto_const_nhds.add
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    have hnum :
        Tendsto (fun _ : ℕ => -(2 * (c : ℝ))) atTop
          (𝓝 (-(2 * (c : ℝ)))) :=
      tendsto_const_nhds
    have h := hnum.div hden (by simpa using hA.ne')
    have heq :
        ((fun _ : ℕ => -(2 * (c : ℝ))) /
          (fun n : ℕ => A + (c : ℝ) / n)) =
        (fun n : ℕ => -(2 * (c : ℝ)) / (A + (c : ℝ) / n)) := by
      funext n
      rfl
    rw [← heq]
    simpa only [add_zero] using h
  have hng :
      Tendsto (fun n : ℕ => (n : ℝ) * g n)
        atTop (𝓝 (-(2 * (c : ℝ)) / A)) := by
    apply hfrac.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    dsimp [g]
    field_simp
  have hpow :=
    (Real.tendsto_one_add_pow_exp_of_tendsto hng).comp
      (tendsto_routeJOnePrimeGeometricScale_atTop hc hp)
  have hpow2 := hpow.pow 2
  convert hpow2 using 1
  · funext j
    change
      Real.tanh (((j + s : ℕ) : ℝ) * Real.log p) ^
          (2 * routeJOnePrimeGeometricScale c p j) =
        ((1 + g (routeJOnePrimeGeometricScale c p j)) ^
          routeJOnePrimeGeometricScale c p j) ^ 2
    rw [show 2 * routeJOnePrimeGeometricScale c p j =
      routeJOnePrimeGeometricScale c p j * 2 by omega, pow_mul]
    congr 2
    rw [tanh_nat_mul_log_prime hp (j + s)]
    dsimp [g, A, routeJOnePrimeGeometricScale]
    push_cast
    rw [pow_add]
    field_simp
    ring_nf
  · rw [← Real.exp_nat_mul]
    congr 1
    dsimp [A]
    ring_nf

theorem routeJOnePrime_scaledPoissonCharacteristic_eq_sqrt
    {c p j s : ℕ} (hp : p.Prime) :
    Real.sqrt (routeJOnePrimeGeometricScale c p j) *
          (semilocalPrimePoissonRatio p ^ (j + s) *
            semilocalArchimedeanCharacteristic
              (((j + s : ℕ) : ℝ) * Real.log p)) =
      Real.sqrt
        (2 * routeJOnePrimeGeometricScale c p j /
          (((p : ℝ) ^ (j + s)) ^ 2 + 1)) := by
  have hk0 : 0 ≤ (routeJOnePrimeGeometricScale c p j : ℝ) := by positivity
  have hprod0 :
      0 ≤ semilocalPrimePoissonRatio p ^ (j + s) *
        semilocalArchimedeanCharacteristic
          (((j + s : ℕ) : ℝ) * Real.log p) :=
    mul_nonneg (pow_nonneg (semilocalPrimePoissonRatio_pos hp).le _)
      (semilocalArchimedeanCharacteristic_pos _).le
  have hden : 0 < (((p : ℝ) ^ (j + s)) ^ 2 + 1) := by positivity
  have hsquare :
      (Real.sqrt (routeJOnePrimeGeometricScale c p j) *
          (semilocalPrimePoissonRatio p ^ (j + s) *
            semilocalArchimedeanCharacteristic
              (((j + s : ℕ) : ℝ) * Real.log p))) ^ 2 =
        2 * routeJOnePrimeGeometricScale c p j /
          (((p : ℝ) ^ (j + s)) ^ 2 + 1) := by
    rw [mul_pow, Real.sq_sqrt hk0,
      semilocalPrimePoissonCharacteristicProduct_sq hp]
    ring
  apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hprod0)
    (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity)]
  exact hsquare

theorem tendsto_routeJOnePrime_scaledPoissonCharacteristic
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime) (s : ℕ) :
    Tendsto
      (fun j =>
        Real.sqrt (routeJOnePrimeGeometricScale c p j) *
          (semilocalPrimePoissonRatio p ^ (j + s) *
            semilocalArchimedeanCharacteristic
              (((j + s : ℕ) : ℝ) * Real.log p)))
      atTop
      (𝓝 (Real.sqrt (2 * (c : ℝ) / (p : ℝ) ^ (2 * s)))) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hinv :
      Tendsto (fun j : ℕ => ((p : ℝ) ^ (2 * j))⁻¹)
        atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp
      (by simpa [pow_mul] using
        (tendsto_pow_atTop_atTop_of_one_lt
          (show (1 : ℝ) < p ^ 2 by nlinarith [sq_nonneg ((p : ℝ) - 1)])))
  have hinside :
      Tendsto
        (fun j : ℕ =>
          2 * routeJOnePrimeGeometricScale c p j /
            (((p : ℝ) ^ (j + s)) ^ 2 + 1))
        atTop
        (𝓝 (2 * (c : ℝ) / (p : ℝ) ^ (2 * s))) := by
    have hbase :
        Tendsto
          (fun j : ℕ =>
            2 * (c : ℝ) /
              ((p : ℝ) ^ (2 * s) + ((p : ℝ) ^ (2 * j))⁻¹))
          atTop
          (𝓝 (2 * (c : ℝ) / (p : ℝ) ^ (2 * s))) := by
      have hden :
          Tendsto
            (fun j : ℕ =>
              (p : ℝ) ^ (2 * s) + ((p : ℝ) ^ (2 * j))⁻¹)
            atTop
            (𝓝 ((p : ℝ) ^ (2 * s) + 0)) :=
        tendsto_const_nhds.add hinv
      have hnum :
          Tendsto (fun _ : ℕ => 2 * (c : ℝ)) atTop
            (𝓝 (2 * (c : ℝ))) :=
        tendsto_const_nhds
      have h := hnum.div hden
        (show (p : ℝ) ^ (2 * s) + 0 ≠ 0 by positivity)
      have heq :
          ((fun _ : ℕ => 2 * (c : ℝ)) /
            (fun j : ℕ =>
              (p : ℝ) ^ (2 * s) + ((p : ℝ) ^ (2 * j))⁻¹)) =
          (fun j : ℕ =>
            2 * (c : ℝ) /
              ((p : ℝ) ^ (2 * s) + ((p : ℝ) ^ (2 * j))⁻¹)) := by
        funext j
        rfl
      rw [← heq]
      simpa only [add_zero] using h
    apply hbase.congr'
    filter_upwards with j
    simp only [routeJOnePrimeGeometricScale]
    push_cast
    rw [pow_add]
    rw [show (p : ℝ) ^ (2 * s) = ((p : ℝ) ^ s) ^ 2 by
      rw [← pow_mul]; congr 1; omega]
    rw [show (p : ℝ) ^ (2 * j) = ((p : ℝ) ^ j) ^ 2 by
      rw [← pow_mul]; congr 1; omega]
    field_simp
  have hsqrt := hinside.sqrt
  apply hsqrt.congr'
  filter_upwards with j
  exact (routeJOnePrime_scaledPoissonCharacteristic_eq_sqrt
    (c := c) (j := j) (s := s) hp).symm

theorem tendsto_routeJOnePrime_scaledRawMagnitude
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime) (s : ℕ) :
    Tendsto
      (fun j =>
        Real.sqrt (routeJOnePrimeGeometricScale c p j) *
          routeJOnePrimeRawMagnitude
            (routeJOnePrimeGeometricScale c p j) p (j + s))
      atTop
      (𝓝
        (Real.sqrt (2 * (c : ℝ) / (p : ℝ) ^ (2 * s)) *
          Real.exp (-4 * (c : ℝ) / (p : ℝ) ^ (2 * s)))) := by
  have hpref :=
    tendsto_routeJOnePrime_scaledPoissonCharacteristic hc hp s
  have htanh := tendsto_routeJOnePrime_geometric_tanhPow hc hp s
  simpa [routeJOnePrimeRawMagnitude, mul_assoc] using hpref.mul htanh

end RHTower



namespace RHTower

theorem routeJOnePrime_sqrt_geometricScale
    {c p j : ℕ} :
    Real.sqrt (routeJOnePrimeGeometricScale c p j) =
      Real.sqrt c * (p : ℝ) ^ j := by
  rw [show (routeJOnePrimeGeometricScale c p j : ℝ) =
      (c : ℝ) * ((p : ℝ) ^ j) ^ 2 by
    simp only [routeJOnePrimeGeometricScale]
    push_cast
    rw [← pow_mul]
    congr 2
    omega]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ c),
    Real.sqrt_sq (by positivity)]

theorem tendsto_routeJOnePrime_scaledRawMagnitude_negativeShift
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime) (d : ℕ) :
    Tendsto
      (fun j =>
        Real.sqrt (routeJOnePrimeGeometricScale c p (j + d)) *
          routeJOnePrimeRawMagnitude
            (routeJOnePrimeGeometricScale c p (j + d)) p j)
      atTop
      (𝓝
        (Real.sqrt (2 * (c : ℝ) * (p : ℝ) ^ (2 * d)) *
          Real.exp (-4 * (c : ℝ) * (p : ℝ) ^ (2 * d)))) := by
  have hc' : 0 < c * p ^ (2 * d) := mul_pos hc (pow_pos hp.pos _)
  have h :=
    tendsto_routeJOnePrime_scaledRawMagnitude
      (c := c * p ^ (2 * d)) hc' hp 0
  have hscale (j : ℕ) :
      routeJOnePrimeGeometricScale c p (j + d) =
        routeJOnePrimeGeometricScale (c * p ^ (2 * d)) p j := by
    simp only [routeJOnePrimeGeometricScale, mul_add, pow_add]
    ring
  convert h using 1
  · funext j
    rw [hscale j]
    simp
  · push_cast
    norm_num
    ring_nf

def routeJOnePrimeNegativeShiftTerm
    (c p j d : ℕ) : ℝ :=
  if d + 1 ≤ j then
    Real.sqrt (routeJOnePrimeGeometricScale c p j) *
      routeJOnePrimeRawMagnitude
        (routeJOnePrimeGeometricScale c p j) p (j - (d + 1))
  else 0

def routeJOnePrimeNegativeProfileAtom
    (c p d : ℕ) : ℝ :=
  Real.sqrt (2 * (c : ℝ) * (p : ℝ) ^ (2 * (d + 1))) *
    Real.exp (-4 * (c : ℝ) * (p : ℝ) ^ (2 * (d + 1)))

theorem tendsto_routeJOnePrimeNegativeShiftTerm
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime) (d : ℕ) :
    Tendsto (fun j => routeJOnePrimeNegativeShiftTerm c p j d)
      atTop (𝓝 (routeJOnePrimeNegativeProfileAtom c p d)) := by
  rw [← tendsto_add_atTop_iff_nat (d + 1)]
  simpa [routeJOnePrimeNegativeShiftTerm,
    routeJOnePrimeNegativeProfileAtom] using
    (tendsto_routeJOnePrime_scaledRawMagnitude_negativeShift hc hp (d + 1))

theorem routeJOnePrimeRawMagnitude_nonneg
    {p : ℕ} (hp : p.Prime) (k M : ℕ) :
    0 ≤ routeJOnePrimeRawMagnitude k p M := by
  unfold routeJOnePrimeRawMagnitude
  exact mul_nonneg
    (mul_nonneg
      (pow_nonneg (semilocalPrimePoissonRatio_pos hp).le M)
      (semilocalArchimedeanCharacteristic_pos _).le)
    (Even.pow_nonneg ⟨k, by omega⟩ _)

theorem routeJOnePrimeNegativeShiftTerm_abs_le
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime) (j d : ℕ) :
    |routeJOnePrimeNegativeShiftTerm c p j d| ≤
      ((p : ℝ)⁻¹) ^ (d + 1) := by
  by_cases hdj : d + 1 ≤ j
  · let D := d + 1
    let M := j - D
    let k := routeJOnePrimeGeometricScale c p j
    have hk : 0 < k := by
      dsimp [k, routeJOnePrimeGeometricScale]
      exact mul_pos hc (pow_pos hp.pos _)
    have hraw :=
      semilocalOnePrimeRawMagnitude_le_low hk hp (M := M)
    have hnonneg :
        0 ≤ Real.sqrt k * routeJOnePrimeRawMagnitude k p M :=
      mul_nonneg (Real.sqrt_nonneg _) (routeJOnePrimeRawMagnitude_nonneg hp _ _)
    have hscaled :
        Real.sqrt k * routeJOnePrimeRawMagnitude k p M ≤
          Real.sqrt k * ((p : ℝ) ^ M / k) :=
      mul_le_mul_of_nonneg_left hraw (Real.sqrt_nonneg _)
    have hMD : M + D = j := by
      dsimp [M, D]
      omega
    have hpPow :
        (p : ℝ) ^ j = (p : ℝ) ^ M * (p : ℝ) ^ D := by
      rw [← pow_add, hMD]
    have hcR : (0 : ℝ) < c := by exact_mod_cast hc
    have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hcR
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hDpow : 0 < (p : ℝ) ^ D := pow_pos hpR _
    have hMpow : 0 < (p : ℝ) ^ M := pow_pos hpR _
    have hscale :
        Real.sqrt k * ((p : ℝ) ^ M / k) =
          (Real.sqrt c)⁻¹ * ((p : ℝ) ^ D)⁻¹ := by
      dsimp [k]
      rw [routeJOnePrime_sqrt_geometricScale, hpPow]
      simp only [routeJOnePrimeGeometricScale]
      push_cast
      rw [show (p : ℝ) ^ (2 * j) = ((p : ℝ) ^ j) ^ 2 by
        rw [← pow_mul]
        congr 1
        omega]
      rw [hpPow, inv_mul_eq_div]
      field_simp
      rw [Real.sq_sqrt hcR.le]
    have hscOne : 1 ≤ Real.sqrt c := by
      rw [Real.le_sqrt (by norm_num) hcR.le]
      exact_mod_cast (Nat.one_le_iff_ne_zero.2 hc.ne')
    have hinvsc : (Real.sqrt c)⁻¹ ≤ 1 :=
      (inv_le_one₀ hsc).2 hscOne
    have hfinal :
        (Real.sqrt c)⁻¹ * ((p : ℝ) ^ D)⁻¹ ≤
          ((p : ℝ) ^ D)⁻¹ :=
      calc
        _ ≤ 1 * ((p : ℝ) ^ D)⁻¹ :=
          mul_le_mul_of_nonneg_right hinvsc (inv_nonneg.mpr hDpow.le)
        _ = _ := one_mul _
    rw [routeJOnePrimeNegativeShiftTerm, if_pos hdj,
      abs_of_nonneg hnonneg]
    change Real.sqrt k * routeJOnePrimeRawMagnitude k p M ≤ _
    calc
      _ ≤ Real.sqrt k * ((p : ℝ) ^ M / k) := hscaled
      _ = (Real.sqrt c)⁻¹ * ((p : ℝ) ^ D)⁻¹ := hscale
      _ ≤ ((p : ℝ) ^ D)⁻¹ := hfinal
      _ = ((p : ℝ)⁻¹) ^ (d + 1) := by
        dsimp [D]
        rw [inv_pow]
  · simp [routeJOnePrimeNegativeShiftTerm, hdj]

theorem summable_routeJOnePrimeNegativeShiftBound
    {p : ℕ} (hp : p.Prime) :
    Summable (fun d : ℕ => ((p : ℝ)⁻¹) ^ (d + 1)) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hq1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpR
  simpa [pow_succ'] using
    (summable_geometric_of_lt_one hq0 hq1).mul_left ((p : ℝ)⁻¹)

theorem tendsto_routeJOnePrimeNegativeShiftTsum
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime) :
    Tendsto
      (fun j => ∑' d : ℕ, routeJOnePrimeNegativeShiftTerm c p j d)
      atTop
      (𝓝 (∑' d : ℕ, routeJOnePrimeNegativeProfileAtom c p d)) := by
  apply tendsto_tsum_of_dominated_convergence
    (summable_routeJOnePrimeNegativeShiftBound hp)
    (tendsto_routeJOnePrimeNegativeShiftTerm hc hp)
  filter_upwards with j d
  simpa [Real.norm_eq_abs] using
    routeJOnePrimeNegativeShiftTerm_abs_le hc hp j d

def routeJOnePrimePositiveShiftTerm
    (c p j s : ℕ) : ℝ :=
  Real.sqrt (routeJOnePrimeGeometricScale c p j) *
    routeJOnePrimeRawMagnitude
      (routeJOnePrimeGeometricScale c p j) p (j + s)

def routeJOnePrimePositiveProfileAtom
    (c p s : ℕ) : ℝ :=
  Real.sqrt (2 * (c : ℝ) / (p : ℝ) ^ (2 * s)) *
    Real.exp (-4 * (c : ℝ) / (p : ℝ) ^ (2 * s))

theorem tendsto_routeJOnePrimePositiveShiftTerm
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime) (s : ℕ) :
    Tendsto (fun j => routeJOnePrimePositiveShiftTerm c p j s)
      atTop (𝓝 (routeJOnePrimePositiveProfileAtom c p s)) := by
  exact tendsto_routeJOnePrime_scaledRawMagnitude hc hp s

theorem routeJOnePrimePositiveShiftTerm_abs_le
    {c p : ℕ} (hp : p.Prime) (j s : ℕ) :
    |routeJOnePrimePositiveShiftTerm c p j s| ≤
      2 * Real.sqrt c * ((p : ℝ)⁻¹) ^ s := by
  let k := routeJOnePrimeGeometricScale c p j
  let M := j + s
  have hraw := semilocalOnePrimeRawMagnitude_le_tail (k := k) hp (M := M)
  have hnonneg :
      0 ≤ Real.sqrt k * routeJOnePrimeRawMagnitude k p M :=
    mul_nonneg (Real.sqrt_nonneg _) (routeJOnePrimeRawMagnitude_nonneg hp _ _)
  have hscaled :
      Real.sqrt k * routeJOnePrimeRawMagnitude k p M ≤
        Real.sqrt k * (2 * ((p : ℝ) ^ M)⁻¹) :=
    mul_le_mul_of_nonneg_left hraw (Real.sqrt_nonneg _)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpj : 0 < (p : ℝ) ^ j := pow_pos hpR _
  have hps : 0 < (p : ℝ) ^ s := pow_pos hpR _
  have hscale :
      Real.sqrt k * (2 * ((p : ℝ) ^ M)⁻¹) =
        2 * Real.sqrt c * ((p : ℝ)⁻¹) ^ s := by
    dsimp [k, M]
    rw [routeJOnePrime_sqrt_geometricScale, pow_add, mul_inv_rev,
      inv_pow]
    field_simp
  rw [routeJOnePrimePositiveShiftTerm, abs_of_nonneg hnonneg]
  change Real.sqrt k * routeJOnePrimeRawMagnitude k p M ≤ _
  exact hscaled.trans_eq hscale

theorem summable_routeJOnePrimePositiveShiftBound
    {c p : ℕ} (hp : p.Prime) :
    Summable (fun s : ℕ => 2 * Real.sqrt c * ((p : ℝ)⁻¹) ^ s) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact (summable_geometric_of_lt_one (by positivity)
    (inv_lt_one_of_one_lt₀ hpR)).mul_left (2 * Real.sqrt c)

theorem tendsto_routeJOnePrimePositiveShiftTsum
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime) :
    Tendsto
      (fun j => ∑' s : ℕ, routeJOnePrimePositiveShiftTerm c p j s)
      atTop
      (𝓝 (∑' s : ℕ, routeJOnePrimePositiveProfileAtom c p s)) := by
  apply tendsto_tsum_of_dominated_convergence
    (summable_routeJOnePrimePositiveShiftBound (c := c) hp)
    (tendsto_routeJOnePrimePositiveShiftTerm hc hp)
  filter_upwards with j s
  simpa [Real.norm_eq_abs] using
    routeJOnePrimePositiveShiftTerm_abs_le (c := c) hp j s

def routeJOnePrimeRawMagnitudeSeries (k p : ℕ) : ℝ :=
  ∑' M : ℕ, routeJOnePrimeRawMagnitude k p M

def routeJOnePrimeGeometricRawProfile (c p : ℕ) : ℝ :=
  (∑' d : ℕ, routeJOnePrimeNegativeProfileAtom c p d) +
    ∑' s : ℕ, routeJOnePrimePositiveProfileAtom c p s

theorem summable_routeJOnePrimeRawMagnitude
    {k p : ℕ} (hp : p.Prime) :
    Summable (fun M : ℕ => routeJOnePrimeRawMagnitude k p M) := by
  let a := semilocalArchimedeanJacobiNormalization (2 * k)
  have ha : 0 < a := semilocalArchimedeanJacobiNormalization_pos _
  have hs := summable_semilocalOnePrimeEvenJacobiMagnitudeTerm (k := k) hp
  have hscaled := hs.mul_left a⁻¹
  have hshift :
      Summable (fun m : ℕ => routeJOnePrimeRawMagnitude k p (m + 1)) := by
    apply hscaled.congr
    intro m
    rw [semilocalOnePrimeEvenJacobiMagnitudeTerm_eq_normalization_mul_raw]
    dsimp [a]
    unfold routeJOnePrimeRawMagnitude
    field_simp [(semilocalArchimedeanJacobiNormalization_pos _).ne']
  exact (summable_nat_add_iff 1).1 (by
    simpa [add_comm] using hshift)

theorem tsum_routeJOnePrimeNegativeShiftTerm_eq_sum_range
    {c p j : ℕ} :
    (∑' d : ℕ, routeJOnePrimeNegativeShiftTerm c p j d) =
      Real.sqrt (routeJOnePrimeGeometricScale c p j) *
        ∑ M ∈ Finset.range j,
          routeJOnePrimeRawMagnitude
            (routeJOnePrimeGeometricScale c p j) p M := by
  rw [tsum_eq_sum (s := Finset.range j) (by
    intro d hd
    have hjd : ¬d + 1 ≤ j := by
      simpa [Nat.not_lt] using hd
    simp [routeJOnePrimeNegativeShiftTerm, hjd])]
  rw [Finset.mul_sum]
  calc
    (∑ d ∈ Finset.range j, routeJOnePrimeNegativeShiftTerm c p j d) =
        ∑ d ∈ Finset.range j,
          Real.sqrt (routeJOnePrimeGeometricScale c p j) *
            routeJOnePrimeRawMagnitude
              (routeJOnePrimeGeometricScale c p j) p (j - 1 - d) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdj : d + 1 ≤ j := by
        have : d < j := Finset.mem_range.1 hd
        omega
      rw [routeJOnePrimeNegativeShiftTerm, if_pos hdj]
      congr 2
      omega
    _ = ∑ M ∈ Finset.range j,
          Real.sqrt (routeJOnePrimeGeometricScale c p j) *
            routeJOnePrimeRawMagnitude
              (routeJOnePrimeGeometricScale c p j) p M :=
      by
        simpa using Finset.sum_range_reflect
          (fun M =>
            Real.sqrt (routeJOnePrimeGeometricScale c p j) *
              routeJOnePrimeRawMagnitude
                (routeJOnePrimeGeometricScale c p j) p M) j

theorem tsum_routeJOnePrimePositiveShiftTerm_eq_tsum_nat_add
    {c p j : ℕ} :
    (∑' s : ℕ, routeJOnePrimePositiveShiftTerm c p j s) =
      Real.sqrt (routeJOnePrimeGeometricScale c p j) *
        ∑' s : ℕ,
          routeJOnePrimeRawMagnitude
            (routeJOnePrimeGeometricScale c p j) p (s + j) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro s
  simp [routeJOnePrimePositiveShiftTerm, add_comm]

theorem routeJOnePrime_scaledRawMagnitudeSeries_eq_shiftTsums
    {c p j : ℕ} (hp : p.Prime) :
    Real.sqrt (routeJOnePrimeGeometricScale c p j) *
        routeJOnePrimeRawMagnitudeSeries
          (routeJOnePrimeGeometricScale c p j) p =
      (∑' d : ℕ, routeJOnePrimeNegativeShiftTerm c p j d) +
        ∑' s : ℕ, routeJOnePrimePositiveShiftTerm c p j s := by
  let k := routeJOnePrimeGeometricScale c p j
  have hs := summable_routeJOnePrimeRawMagnitude (k := k) hp
  have hsplit := hs.sum_add_tsum_nat_add j
  rw [tsum_routeJOnePrimeNegativeShiftTerm_eq_sum_range,
    tsum_routeJOnePrimePositiveShiftTerm_eq_tsum_nat_add]
  unfold routeJOnePrimeRawMagnitudeSeries
  change Real.sqrt k * (∑' M : ℕ, routeJOnePrimeRawMagnitude k p M) =
    Real.sqrt k * (∑ M ∈ Finset.range j, routeJOnePrimeRawMagnitude k p M) +
      Real.sqrt k * (∑' s : ℕ, routeJOnePrimeRawMagnitude k p (s + j))
  rw [← mul_add, hsplit]

theorem tendsto_routeJOnePrime_scaledRawMagnitudeSeries
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime) :
    Tendsto
      (fun j =>
        Real.sqrt (routeJOnePrimeGeometricScale c p j) *
          routeJOnePrimeRawMagnitudeSeries
            (routeJOnePrimeGeometricScale c p j) p)
      atTop
      (𝓝 (routeJOnePrimeGeometricRawProfile c p)) := by
  have h :=
    (tendsto_routeJOnePrimeNegativeShiftTsum hc hp).add
      (tendsto_routeJOnePrimePositiveShiftTsum hc hp)
  apply h.congr'
  filter_upwards with j
  exact (routeJOnePrime_scaledRawMagnitudeSeries_eq_shiftTsums hp).symm

theorem routeJOnePrimeGeometricRawProfile_mul_prime_sq
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime) :
    routeJOnePrimeGeometricRawProfile (c * p ^ 2) p =
      routeJOnePrimeGeometricRawProfile c p := by
  have hc' : 0 < c * p ^ 2 := mul_pos hc (pow_pos hp.pos _)
  have hnew :=
    tendsto_routeJOnePrime_scaledRawMagnitudeSeries hc' hp
  have hold :=
    tendsto_routeJOnePrime_scaledRawMagnitudeSeries hc hp
  have hshift :
      Tendsto
        (fun j =>
          Real.sqrt (routeJOnePrimeGeometricScale c p (j + 1)) *
            routeJOnePrimeRawMagnitudeSeries
              (routeJOnePrimeGeometricScale c p (j + 1)) p)
        atTop
        (𝓝 (routeJOnePrimeGeometricRawProfile c p)) :=
    (tendsto_add_atTop_iff_nat 1).2 hold
  have heq (j : ℕ) :
      routeJOnePrimeGeometricScale (c * p ^ 2) p j =
        routeJOnePrimeGeometricScale c p (j + 1) := by
    simp [routeJOnePrimeGeometricScale, mul_add, pow_add]
    ring
  have hnew' :
      Tendsto
        (fun j =>
          Real.sqrt (routeJOnePrimeGeometricScale c p (j + 1)) *
            routeJOnePrimeRawMagnitudeSeries
              (routeJOnePrimeGeometricScale c p (j + 1)) p)
        atTop
        (𝓝 (routeJOnePrimeGeometricRawProfile (c * p ^ 2) p)) := by
    apply hnew.congr'
    filter_upwards with j
    rw [heq j]
  exact tendsto_nhds_unique hnew' hshift



end RHTower

namespace RHTower

theorem routeJOnePrimeRawMagnitude_zero
    {k p : ℕ} (hk : 0 < k) :
    routeJOnePrimeRawMagnitude k p 0 = 0 := by
  simp [routeJOnePrimeRawMagnitude, hk.ne']

theorem semilocalOnePrimeEvenJacobiMagnitudeSeries_eq_normalization_mul_rawSeries
    {k p : ℕ} (hk : 0 < k) (hp : p.Prime) :
    semilocalOnePrimeEvenJacobiMagnitudeSeries k p =
      semilocalArchimedeanJacobiNormalization (2 * k) *
        routeJOnePrimeRawMagnitudeSeries k p := by
  have hs := summable_routeJOnePrimeRawMagnitude (k := k) hp
  have hsplit := hs.sum_add_tsum_nat_add 1
  have hshift :
      (∑' m : ℕ, routeJOnePrimeRawMagnitude k p (m + 1)) =
        routeJOnePrimeRawMagnitudeSeries k p := by
    unfold routeJOnePrimeRawMagnitudeSeries
    simpa [routeJOnePrimeRawMagnitude_zero hk, add_comm] using hsplit
  unfold semilocalOnePrimeEvenJacobiMagnitudeSeries
  calc
    (∑' m : ℕ, semilocalOnePrimeEvenJacobiMagnitudeTerm k p m) =
        ∑' m : ℕ,
          semilocalArchimedeanJacobiNormalization (2 * k) *
            routeJOnePrimeRawMagnitude k p (m + 1) := by
      apply tsum_congr
      exact semilocalOnePrimeEvenJacobiMagnitudeTerm_eq_normalization_mul_raw k p
    _ = semilocalArchimedeanJacobiNormalization (2 * k) *
        (∑' m : ℕ, routeJOnePrimeRawMagnitude k p (m + 1)) :=
      tsum_mul_left
    _ = _ := by rw [hshift]

def routeJOnePrimeIntrinsicNormalizedCoefficient
    (k p : ℕ) : ℝ :=
  Real.sqrt k * |semilocalOnePrimeEvenJacobiCoefficient k p| /
    (2 * (1 - semilocalPrimePoissonRatio p ^ 2)⁻¹ *
      semilocalArchimedeanJacobiNormalization (2 * k))

theorem routeJOnePrimeIntrinsicNormalizedCoefficient_eq_scaledRawSeries
    {k p : ℕ} (hk : 0 < k) (hp : p.Prime) :
    routeJOnePrimeIntrinsicNormalizedCoefficient k p =
      Real.sqrt k * routeJOnePrimeRawMagnitudeSeries k p := by
  let P : ℝ := 2 * (1 - semilocalPrimePoissonRatio p ^ 2)⁻¹
  let a : ℝ := semilocalArchimedeanJacobiNormalization (2 * k)
  have hP : 0 < P := lt_of_lt_of_le (by norm_num)
    (semilocalOnePrimePoissonCoefficientPrefactor_bounds hp).1
  have ha : 0 < a := semilocalArchimedeanJacobiNormalization_pos _
  have hcoeff :
      |semilocalOnePrimeEvenJacobiCoefficient k p| =
        P * semilocalOnePrimeEvenJacobiMagnitudeSeries k p := by
    dsimp [P]
    exact abs_semilocalOnePrimeEvenJacobiCoefficient_eq_magnitudeSeries hk hp
  unfold routeJOnePrimeIntrinsicNormalizedCoefficient
  change Real.sqrt k * |semilocalOnePrimeEvenJacobiCoefficient k p| /
    (P * a) = _
  rw [hcoeff,
    semilocalOnePrimeEvenJacobiMagnitudeSeries_eq_normalization_mul_rawSeries
      hk hp]
  field_simp [hP.ne', ha.ne']
  dsimp [a]
  ring

theorem tendsto_routeJOnePrimeIntrinsicNormalizedCoefficient_geometric
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime) :
    Tendsto
      (fun j =>
        routeJOnePrimeIntrinsicNormalizedCoefficient
          (routeJOnePrimeGeometricScale c p j) p)
      atTop
      (𝓝 (routeJOnePrimeGeometricRawProfile c p)) := by
  have h := tendsto_routeJOnePrime_scaledRawMagnitudeSeries hc hp
  apply h.congr'
  filter_upwards with j
  exact (routeJOnePrimeIntrinsicNormalizedCoefficient_eq_scaledRawSeries
    (hp := hp) (by
      unfold routeJOnePrimeGeometricScale
      exact mul_pos hc (pow_pos hp.pos _))).symm



end RHTower

namespace RHTower

theorem summable_routeJOnePrimePositiveProfileAtom
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime) :
    Summable (routeJOnePrimePositiveProfileAtom c p) := by
  apply Summable.of_nonneg_of_le
    (fun s => by
      unfold routeJOnePrimePositiveProfileAtom
      positivity)
    (fun s => ?_)
    (summable_routeJOnePrimePositiveShiftBound (c := c) hp)
  have hlim :=
    (tendsto_norm.comp
      (tendsto_routeJOnePrimePositiveShiftTerm hc hp s))
  have hle :
      ‖routeJOnePrimePositiveProfileAtom c p s‖ ≤
        2 * Real.sqrt c * ((p : ℝ)⁻¹) ^ s :=
    le_of_tendsto hlim (by
      filter_upwards with j
      simpa [Real.norm_eq_abs] using
        routeJOnePrimePositiveShiftTerm_abs_le (c := c) hp j s)
  have hatom0 : 0 ≤ routeJOnePrimePositiveProfileAtom c p s := by
    unfold routeJOnePrimePositiveProfileAtom
    positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg hatom0] using hle

theorem summable_routeJOnePrimeNegativeProfileAtom
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime) :
    Summable (routeJOnePrimeNegativeProfileAtom c p) := by
  apply Summable.of_nonneg_of_le
    (fun d => by
      unfold routeJOnePrimeNegativeProfileAtom
      positivity)
    (fun d => ?_)
    (summable_routeJOnePrimeNegativeShiftBound hp)
  have hlim :=
    (tendsto_norm.comp
      (tendsto_routeJOnePrimeNegativeShiftTerm hc hp d))
  have hle :
      ‖routeJOnePrimeNegativeProfileAtom c p d‖ ≤
        ((p : ℝ)⁻¹) ^ (d + 1) :=
    le_of_tendsto hlim (by
      filter_upwards with j
      simpa [Real.norm_eq_abs] using
        routeJOnePrimeNegativeShiftTerm_abs_le hc hp j d)
  have hatom0 : 0 ≤ routeJOnePrimeNegativeProfileAtom c p d := by
    unfold routeJOnePrimeNegativeProfileAtom
    positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg hatom0] using hle

theorem routeJOnePrimeGeometricRawProfile_pos
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime) :
    0 < routeJOnePrimeGeometricRawProfile c p := by
  have hpos :
      0 < ∑' s : ℕ, routeJOnePrimePositiveProfileAtom c p s :=
    (summable_routeJOnePrimePositiveProfileAtom hc hp).tsum_pos
      (fun s => by
        unfold routeJOnePrimePositiveProfileAtom
        positivity)
      0
      (by
        unfold routeJOnePrimePositiveProfileAtom
        have hcR : (0 : ℝ) < c := by exact_mod_cast hc
        exact mul_pos (Real.sqrt_pos.2 (by norm_num; positivity)) (Real.exp_pos _))
  unfold routeJOnePrimeGeometricRawProfile
  exact add_pos_of_nonneg_of_pos
    (tsum_nonneg fun d => by
      unfold routeJOnePrimeNegativeProfileAtom
      positivity)
    hpos


end RHTower
