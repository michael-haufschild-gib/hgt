import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheMertensEnergyPaysItsCriticalResidues
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheZeroForcesALogarithmicFloor
import GaloisForLFunctions.RHTower.MobiusMertensMeanSquareExponentLaw

/-!
# The long Möbius polynomial pays for the negative moments

For the long Möbius polynomial `M_n(½) = Σ_{k ≤ n} μ(k) k^{−1/2}` and every finite set `Z` of simple zeros
on the critical line,

`limsup_{T→∞} (log T)⁻¹ Σ_{n ≤ T} |M_n(½)|²/n ≥ ¼ Σ_{ρ ∈ Z} |ρ ζ′(ρ)|^{−2}`

(`not_forall_moebiusPoly_energy_le`), with no hypothesis.

**Mechanism.** Abel summation expresses the Mertens function through the polynomial,
`M(n) = √n A(n) − Σ_{k<n} (√(k+1) − √k) A(k)`, and a discrete Hardy inequality bounds the Mertens
pronic energy by four times the log energy of `A` (`sum_mertensRow_sq_le`). The Mertens energy pays its
critical residues (`not_forall_mertens_pronicEnergy_le_log`).

**The link.** A long-Möbius second moment with logarithmic slope `S` at the central point bounds the
negative second moment `Σ_ρ |ρζ′(ρ)|^{−2}` over the simple critical zeros by `4S`. So this branch of WD
cannot be reached without controlling the small values of `ζ′` at the zeros.
-/

noncomputable section

open Complex Set Filter
open ArithmeticFunction (moebius)
open GaloisForLFunctions.ArithmeticCorrespondencePositivity

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The real Möbius polynomial `A(n) = Σ_{k ≤ n} μ(k) k^{−1/2}` at the central point. -/
def centralMoebius (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, (moebius k : ℝ) / Real.sqrt k

theorem centralMoebius_zero : centralMoebius 0 = 0 := by
  simp [centralMoebius]

theorem centralMoebius_succ (n : ℕ) :
    centralMoebius (n + 1) = centralMoebius n + (moebius (n + 1) : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ) := by
  unfold centralMoebius
  rw [Finset.sum_Icc_succ_top (by omega)]

/-- The polynomial `moebiusPoly` at the central point is the real sum. -/
theorem moebiusPoly_linePoint_zero (n : ℕ) :
    moebiusPoly n (linePoint 0) = ((centralMoebius n : ℝ) : ℂ) := by
  unfold centralMoebius
  rw [Complex.ofReal_sum]
  show ∑ k ∈ Finset.Icc 1 n, RHTower.mobCoeff k * ((k : ℝ) : ℂ) ^ (-linePoint 0) = _
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  have e1 : -linePoint 0 = ((-(1 / 2) : ℝ) : ℂ) := by
    unfold linePoint
    push_cast
    ring
  have e2 : (k : ℝ) ^ (-(1 / 2) : ℝ) = (Real.sqrt k)⁻¹ := by
    rw [Real.rpow_neg hk0.le, Real.sqrt_eq_rpow]
  rw [e1, ← Complex.ofReal_cpow hk0.le, e2]
  unfold RHTower.mobCoeff
  push_cast
  rw [div_eq_mul_inv]

/-- **Abel summation.** `M(n) = √n A(n) − Σ_{k<n} (√(k+1) − √k) A(k)`. -/
theorem mertensRow_eq_abel (n : ℕ) :
    mertensRow n = Real.sqrt n * centralMoebius n -
      ∑ k ∈ Finset.range n, (Real.sqrt ((k : ℝ) + 1) - Real.sqrt k) * centralMoebius k := by
  induction n with
  | zero => simp [mertensRow_zero, centralMoebius_zero]
  | succ n ih =>
    have hM : mertensRow (n + 1) = mertensRow n + (moebius (n + 1) : ℝ) := by
      unfold mertensRow
      exact prefixSum_succ _ n
    have hpos : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    rw [hM, ih, Finset.sum_range_succ, centralMoebius_succ]
    push_cast
    field_simp
    ring

/-- The gaps of the square root. -/
def rootGap (k : ℕ) : ℝ := Real.sqrt ((k : ℝ) + 1) - Real.sqrt k

theorem rootGap_nonneg (k : ℕ) : 0 ≤ rootGap k :=
  sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))

theorem sum_rootGap (n : ℕ) : ∑ k ∈ Finset.range n, rootGap k = Real.sqrt n := by
  have h := Finset.sum_range_sub (fun k : ℕ => Real.sqrt k) n
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, Real.sqrt_zero, sub_zero] at h
  exact h

/-- `√(k+1) − √k ≤ 1/(2√k)`. -/
theorem rootGap_le {k : ℕ} (hk : 1 ≤ k) : rootGap k ≤ 1 / (2 * Real.sqrt k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hs1 : Real.sqrt k ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  have h1 : Real.sqrt ((k : ℝ) + 1) ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have h2 : Real.sqrt (k : ℝ) ^ 2 = k := Real.sq_sqrt hk0.le
  unfold rootGap
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- The energy increment at scale `k`. -/
def walkEnergy (k : ℕ) : ℝ := rootGap k * centralMoebius k ^ 2

theorem walkEnergy_nonneg (k : ℕ) : 0 ≤ walkEnergy k :=
  mul_nonneg (rootGap_nonneg k) (sq_nonneg _)

/-- The energy is cumulative in the scale. -/
def cumulativeEnergy (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, walkEnergy k

theorem cumulativeEnergy_nonneg (n : ℕ) : 0 ≤ cumulativeEnergy n :=
  Finset.sum_nonneg fun k _ => walkEnergy_nonneg k

/-- The square of the Mertens function, through Abel and Cauchy–Schwarz. -/
theorem mertensRow_sq_le (n : ℕ) :
    mertensRow n ^ 2 ≤ 2 * n * centralMoebius n ^ 2 + 2 * Real.sqrt n * cumulativeEnergy n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hcs := RHTower.sq_sum_mul_le_sum_sq_mul_mul_sum (Finset.range n) centralMoebius rootGap
    rootGap_nonneg
  rw [sum_rootGap] at hcs
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = ∑ k ∈ Finset.range n, centralMoebius k * rootGap k := ⟨_, rfl⟩
  rw [← hb] at hcs
  have hE : ∑ k ∈ Finset.range n, centralMoebius k ^ 2 * rootGap k = cumulativeEnergy n := by
    unfold cumulativeEnergy walkEnergy
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hE] at hcs
  have hsum : ∑ k ∈ Finset.range n, (Real.sqrt ((k : ℝ) + 1) - Real.sqrt k) * centralMoebius k = b := by
    rw [hb]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [mertensRow_eq_abel, hsum]
  have hs : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn
  nlinarith [sq_nonneg (Real.sqrt (n : ℝ) * centralMoebius n + b)]

/-- The Hardy weight `1/(√n (n+1))`. -/
def hardyWeight (n : ℕ) : ℝ := 1 / (Real.sqrt n * ((n : ℝ) + 1))

/-- The Hardy weight telescopes: `1/(√(T+1)(T+2)) ≤ 2/√T − 2/√(T+1)`. -/
theorem hardyWeight_succ_le {T : ℕ} (hT : 1 ≤ T) :
    hardyWeight (T + 1) ≤ 2 / Real.sqrt T - 2 / Real.sqrt ((T + 1 : ℕ) : ℝ) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.sqrt T := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.sqrt ((T + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hx0 : 0 < x := hx ▸ Real.sqrt_pos.mpr hT0
  have hy0 : 0 < y := hy ▸ Real.sqrt_pos.mpr (by positivity)
  have hx2 : x ^ 2 = T := by
    rw [hx]
    exact Real.sq_sqrt hT0.le
  have hy2 : y ^ 2 = (T : ℝ) + 1 := by
    rw [hy]
    push_cast
    exact Real.sq_sqrt (by positivity)
  have hxy : x ≤ y := by
    rw [hx, hy]
    refine Real.sqrt_le_sqrt ?_
    push_cast
    linarith
  unfold hardyWeight
  rw [← hx, ← hy]
  have e0 : (((T + 1 : ℕ) : ℝ) + 1) = y ^ 2 + 1 := by
    push_cast
    linarith
  rw [e0, div_sub_div _ _ hx0.ne' hy0.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  have hgap : y - x = 1 / (y + x) := by
    field_simp
    nlinarith
  have e1 : 2 * y - x * 2 = 2 * (y - x) := by ring
  rw [e1, hgap]
  have hsum : 0 < y + x := by positivity
  have e2 : 2 * (1 / (y + x)) * (y * (y ^ 2 + 1)) = 2 * (y * (y ^ 2 + 1)) / (y + x) := by ring
  rw [one_mul, e2, le_div_iff₀ hsum]
  have h1 : x * y ≤ y * y := mul_le_mul_of_nonneg_right hxy hy0.le
  have h2 : y + x ≤ y + y := by linarith
  have h3 := mul_le_mul h1 h2 hsum.le (by positivity)
  nlinarith

theorem hardyWeight_nonneg (n : ℕ) : 0 ≤ hardyWeight n := by
  unfold hardyWeight
  positivity

theorem pronic_term_algebra {A E s : ℝ} (hs : 0 < s) :
    (2 * (A ^ 2 / (s * s)) + 2 * (1 / (s * (s * s + 1)) * E)) * ((s * s) * (s * s + 1)) =
      2 * (s * s + 1) * A ^ 2 + 2 * s * E := by
  field_simp

/-- A term of the Mertens pronic energy. -/
theorem mertens_term_le {n : ℕ} (hn : 1 ≤ n) :
    mertensRow n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      2 * (centralMoebius n ^ 2 / n) + 2 * (hardyWeight n * cumulativeEnergy n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hs2 : Real.sqrt (n : ℝ) * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have hden : 0 < (n : ℝ) * ((n : ℝ) + 1) := by positivity
  rw [div_le_iff₀ hden]
  refine (mertensRow_sq_le n).trans ?_
  unfold hardyWeight
  have e1 : (2 * (centralMoebius n ^ 2 / n) + 2 * (1 / (Real.sqrt n * ((n : ℝ) + 1)) * cumulativeEnergy n)) *
      ((n : ℝ) * ((n : ℝ) + 1)) =
      2 * ((n : ℝ) + 1) * centralMoebius n ^ 2 + 2 * Real.sqrt n * cumulativeEnergy n := by
    have h := pronic_term_algebra (A := centralMoebius n) (E := cumulativeEnergy n) hs
    rwa [hs2] at h
  rw [e1]
  nlinarith [sq_nonneg (centralMoebius n)]

/-- **Discrete Hardy.** The weighted cumulative energy is dominated by the energy with weight `2/√k`. -/
theorem sum_hardyWeight_mul_cumulative_le {T : ℕ} (hT : 1 ≤ T) :
    ∑ n ∈ Finset.Icc 1 T, hardyWeight n * cumulativeEnergy n ≤
      ∑ k ∈ Finset.range T, walkEnergy k * (2 / Real.sqrt k - 2 / Real.sqrt T) := by
  induction T, hT using Nat.le_induction with
  | base =>
    simp [cumulativeEnergy, walkEnergy, centralMoebius_zero]
  | succ T hT ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ]
    have hδ := hardyWeight_succ_le hT
    obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 2 / Real.sqrt T - 2 / Real.sqrt ((T + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
    rw [← hδdef] at hδ
    have hsplit : ∑ k ∈ Finset.range T, walkEnergy k *
        (2 / Real.sqrt k - 2 / Real.sqrt ((T + 1 : ℕ) : ℝ)) =
        ∑ k ∈ Finset.range T, walkEnergy k * (2 / Real.sqrt k - 2 / Real.sqrt T) +
          cumulativeEnergy T * δ := by
      unfold cumulativeEnergy
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hδdef]
      ring
    have hlast : walkEnergy T * (2 / Real.sqrt T - 2 / Real.sqrt ((T + 1 : ℕ) : ℝ)) =
        walkEnergy T * δ := by
      rw [hδdef]
    rw [hsplit, hlast]
    have hstep : hardyWeight (T + 1) * cumulativeEnergy (T + 1) ≤ cumulativeEnergy (T + 1) * δ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hδ (cumulativeEnergy_nonneg _)
    have hcum : cumulativeEnergy (T + 1) = cumulativeEnergy T + walkEnergy T := by
      unfold cumulativeEnergy
      rw [Finset.sum_range_succ]
    rw [hcum] at hstep ⊢
    nlinarith

/-- The energy with weight `2/√k` is dominated by the log energy of `A`. -/
theorem walkEnergy_mul_le (k : ℕ) :
    walkEnergy k * (2 / Real.sqrt k) ≤ centralMoebius k ^ 2 / k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [walkEnergy, centralMoebius_zero]
  · have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hs : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
    have hg := rootGap_le hk
    have hs2 : Real.sqrt (k : ℝ) * Real.sqrt k = k := Real.mul_self_sqrt hk0.le
    unfold walkEnergy
    calc rootGap k * centralMoebius k ^ 2 * (2 / Real.sqrt k)
        ≤ 1 / (2 * Real.sqrt k) * centralMoebius k ^ 2 * (2 / Real.sqrt k) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hg (sq_nonneg _)) (by positivity)
      _ = centralMoebius k ^ 2 / (Real.sqrt k * Real.sqrt k) := by
          field_simp
      _ = _ := by rw [hs2]

/-- **The Mertens pronic energy is at most four times the log energy of the Möbius polynomial.** -/
theorem sum_mertensRow_sq_le (T : ℕ) :
    ∑ n ∈ Finset.Icc 1 T, mertensRow n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      4 * ∑ n ∈ Finset.Icc 1 T, centralMoebius n ^ 2 / n := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  have hterm := Finset.sum_le_sum (s := Finset.Icc 1 T) fun n hn =>
    mertens_term_le (Finset.mem_Icc.mp hn).1
  refine hterm.trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hH := sum_hardyWeight_mul_cumulative_le hT
  have hdrop : ∑ k ∈ Finset.range T, walkEnergy k * (2 / Real.sqrt k - 2 / Real.sqrt T) ≤
      ∑ k ∈ Finset.range T, centralMoebius k ^ 2 / k := by
    refine Finset.sum_le_sum fun k _ => le_trans ?_ (walkEnergy_mul_le k)
    refine mul_le_mul_of_nonneg_left ?_ (walkEnergy_nonneg k)
    have : 0 ≤ 2 / Real.sqrt (T : ℝ) := by positivity
    linarith
  have hrange : ∑ k ∈ Finset.range T, centralMoebius k ^ 2 / k ≤
      ∑ n ∈ Finset.Icc 1 T, centralMoebius n ^ 2 / n := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hT]
    simp only [Nat.cast_zero, div_zero, zero_add]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => by positivity
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hn
    exact Finset.mem_Icc.mpr ⟨h1, h2.le⟩
  linarith

/-- **The long Möbius polynomial pays for the negative moments.** For every finite set `Z` of simple
critical zeros and every `S < ¼ Σ_{ρ ∈ Z} |ρ ζ′(ρ)|^{−2}`, the log energy
`Σ_{n ≤ T} |M_n(½)|²/n` is not bounded by `S log(T+1) + B`. -/
theorem not_forall_moebiusPoly_energy_le (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ deriv riemannZeta ρ ≠ 0 ∧ ρ.re = 1 / 2) {S B : ℝ}
    (hS : S < 1 / 4 * ∑ ρ ∈ Z, ‖1 / (ρ * deriv riemannZeta ρ)‖ ^ 2) :
    ¬ ∀ T : ℕ, ∑ n ∈ Finset.Icc 1 T, ‖moebiusPoly n (linePoint 0)‖ ^ 2 / n ≤
      S * Real.log ((T : ℝ) + 1) + B := by
  intro hall
  refine not_forall_mertens_pronicEnergy_le_log Z hZ (S := 4 * S) (B := 4 * B) (by linarith) ?_
  intro T
  refine (sum_mertensRow_sq_le T).trans ?_
  have h := hall T
  have e : ∑ n ∈ Finset.Icc 1 T, ‖moebiusPoly n (linePoint 0)‖ ^ 2 / n =
      ∑ n ∈ Finset.Icc 1 T, centralMoebius n ^ 2 / n := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [moebiusPoly_linePoint_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [e] at h
  linarith

end GaloisForLFunctions.MultiscaleMollifiedZetaField
