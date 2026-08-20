/-
# The closure of the determinant graph on the operator side

The order-`p` regularized determinant of an operator is the determinant of its power-trace
sequence, so the closure statement for a power-trace sequence applies verbatim once two things are
supplied: a uniform geometric bound on the power traces, which the Schatten norm gives through the
trace norm of a power, and their convergence, which the telescoping estimate gives.  No
self-adjointness and no spectral decomposition is used.

Main results:
* `opSchattenDet_eq_tracePowerDet` — the operator determinant is the determinant of its traces.
* `norm_le_schattenNorm`, `schattenNorm_rpow_eq_tsum` — the Schatten norm dominates the operator
  norm and carries the `p`-energy.
* `norm_opTrace_pow_add_le` — **the uniform geometric bound on the power traces**.
* `exists_poly_limit_of_tendsto_opSchattenDet` — **the closure of the determinant graph, with the
  operators presented in the Schatten topology**.
-/
import GaloisForLFunctions.HTGeometry.TracePowerDeterminantGraphClosure
import GaloisForLFunctions.HTGeometry.SchattenPowerTraceContinuity
import GaloisForLFunctions.HTGeometry.SchattenOperatorDeterminant

open Filter Topology Metric ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The operator determinant is the determinant of its power traces -/

theorem opSchattenDetExp_eq_tracePowerDetExp (p : ℕ) (T : H →L[ℂ] H) (z : ℂ) :
    opSchattenDetExp p T z = tracePowerDetExp p (fun m => opTrace (T ^ m)) z := rfl

theorem opSchattenDet_eq_tracePowerDet (p : ℕ) (T : H →L[ℂ] H) (z : ℂ) :
    opSchattenDet p T z = tracePowerDet p (fun m => opTrace (T ^ m)) z := rfl

/-! ## The Schatten norm dominates the operator norm -/

omit [CompleteSpace H] in
theorem norm_le_schattenNorm {p : ℝ} (hp : 0 < p) {T : H →L[ℂ] H} (hT : MemSchattenClass p T) :
    ‖T‖ ≤ schattenNorm p T := by
  have hnn : ∀ n : ℕ, 0 ≤ approxNumber T n ^ p := fun n =>
    Real.rpow_nonneg (approxNumber_nonneg T n) p
  have hle : approxNumber T 0 ^ p ≤ ∑' n, approxNumber T n ^ p :=
    hT.le_tsum 0 fun n _ => hnn n
  have h0 : approxNumber T 0 = ‖T‖ := approxNumber_zero_eq_norm T
  rw [h0] at hle
  have hsum0 : (0 : ℝ) ≤ ∑' n, approxNumber T n ^ p := tsum_nonneg hnn
  rw [schattenNorm]
  calc ‖T‖ = (‖T‖ ^ p) ^ (1 / p) := by
        rw [← Real.rpow_mul (norm_nonneg T), mul_one_div, div_self hp.ne', Real.rpow_one]
    _ ≤ (∑' n, approxNumber T n ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg T) p) hle (by positivity)

omit [CompleteSpace H] in
theorem schattenNorm_rpow_eq_tsum {p : ℝ} (hp : 0 < p) (T : H →L[ℂ] H) :
    (schattenNorm p T) ^ p = ∑' n, approxNumber T n ^ p := by
  have hsum0 : (0 : ℝ) ≤ ∑' n, approxNumber T n ^ p :=
    tsum_nonneg fun n => Real.rpow_nonneg (approxNumber_nonneg T n) p
  rw [schattenNorm, ← Real.rpow_mul hsum0, one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]

/-! ## The uniform geometric bound on the power traces -/

omit [CompleteSpace H] in
theorem memSchattenClass_one_pow_add {p : ℕ} (hp : 0 < p) {T : H →L[ℂ] H}
    (hT : MemSchattenClass (p : ℝ) T) (k : ℕ) : MemSchattenClass 1 (T ^ (k + p)) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hkp : 0 < k + p := by omega
  have hpow := memSchattenClass_pow hpR hT hkp
  refine hpow.mono (by positivity) ?_
  rw [div_le_one (by positivity : (0 : ℝ) < ((k + p : ℕ) : ℝ))]
  push_cast
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

/-- **The power traces obey a geometric bound in the Schatten norm.** -/
theorem norm_opTrace_pow_add_le {p : ℕ} (hp : 0 < p) {T : H →L[ℂ] H}
    (hT : MemSchattenClass (p : ℝ) T) {C : ℝ} (hC1 : 1 ≤ C)
    (hC : schattenNorm (p : ℝ) T ≤ C) (k : ℕ) :
    ‖opTrace (T ^ (k + p))‖ ≤ ((1 + (p : ℝ)) * C ^ (p : ℝ)) * (2 * C) ^ k := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hkp : 0 < k + p := by omega
  have hpk : (p : ℝ) ≤ ((k + p : ℕ) : ℝ) := by
    push_cast
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have h1 : ‖opTrace (T ^ (k + p))‖ ≤ traceNorm H (T ^ (k + p)) :=
    norm_opTrace_le_traceNorm (memSchattenClass_one_pow_add hp hT k)
  have h2 := traceNorm_pow_le hpR hT hkp hpk
  set M : ℝ := max ‖T‖ 1 with hM
  set E : ℝ := ∑' n, approxNumber T n ^ (p : ℝ) with hE
  have hM1 : (1 : ℝ) ≤ M := le_max_right _ _
  have hE0 : (0 : ℝ) ≤ E := tsum_nonneg fun n => Real.rpow_nonneg (approxNumber_nonneg T n) _
  -- the exponent of `M` is the natural power `k`
  have hexp : M ^ (((k + p : ℕ) : ℝ) - (p : ℝ)) = M ^ k := by
    have harg : ((k + p : ℕ) : ℝ) - (p : ℝ) = ((k : ℕ) : ℝ) := by push_cast; ring
    rw [harg, Real.rpow_natCast]
  rw [hexp] at h2
  -- the Schatten norm dominates both `M` and the `p`-energy
  have hnormle : ‖T‖ ≤ C := le_trans (norm_le_schattenNorm hpR hT) hC
  have hMC : M ≤ C := max_le hnormle hC1
  have hEC : E ≤ C ^ (p : ℝ) := by
    rw [hE, ← schattenNorm_rpow_eq_tsum hpR T]
    exact Real.rpow_le_rpow (schattenNorm_nonneg _ _) hC hpR.le
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  have hCp0 : (0 : ℝ) ≤ C ^ (p : ℝ) := (Real.rpow_pos_of_pos hC0 _).le
  have hMk : M ^ k ≤ C ^ k := pow_le_pow_left₀ (by linarith) hMC k
  have hMk0 : (0 : ℝ) ≤ M ^ k := pow_nonneg (by linarith) k
  -- the count `k + p` is absorbed by a factor two per step
  have hcount : ((k + p : ℕ) : ℝ) ≤ (1 + (p : ℝ)) * 2 ^ k := by
    have hk2 : (k : ℝ) + 1 ≤ 2 ^ k := by
      have hnat : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
      have hcast : ((k + 1 : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast at hcast
      linarith
    have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hpnn : (0 : ℝ) ≤ (p : ℝ) := hpR.le
    have hp2 : (p : ℝ) * 1 ≤ (p : ℝ) * 2 ^ k := mul_le_mul_of_nonneg_left h2k hpnn
    push_cast
    linarith [hk2, hp2]
  have hfin : ((k + p : ℕ) : ℝ) * (M ^ k * E) ≤ ((1 + (p : ℝ)) * C ^ (p : ℝ)) * (2 * C) ^ k := by
    have hstep1 : M ^ k * E ≤ C ^ k * C ^ (p : ℝ) :=
      mul_le_mul hMk hEC hE0 (pow_nonneg hC0.le k)
    have hnn1 : (0 : ℝ) ≤ M ^ k * E := mul_nonneg hMk0 hE0
    have hkpnn : (0 : ℝ) ≤ ((k + p : ℕ) : ℝ) := Nat.cast_nonneg _
    have hprod : ((k + p : ℕ) : ℝ) * (M ^ k * E)
        ≤ ((1 + (p : ℝ)) * 2 ^ k) * (C ^ k * C ^ (p : ℝ)) :=
      mul_le_mul hcount hstep1 hnn1 (by positivity)
    have hrw : ((1 + (p : ℝ)) * 2 ^ k) * (C ^ k * C ^ (p : ℝ))
        = ((1 + (p : ℝ)) * C ^ (p : ℝ)) * (2 * C) ^ k := by
      rw [mul_pow]
      ring
    linarith [hprod, hrw.le, hrw.ge]
  calc ‖opTrace (T ^ (k + p))‖ ≤ traceNorm H (T ^ (k + p)) := h1
    _ ≤ ((k + p : ℕ) : ℝ) * (M ^ k * E) := h2
    _ ≤ ((1 + (p : ℝ)) * C ^ (p : ℝ)) * (2 * C) ^ k := hfin

/-! ## The closure of the determinant graph in the Schatten topology -/

/-- **The order-`p` determinant is continuous in the Schatten norm.** -/
theorem tendsto_opSchattenDet_of_tendsto_schattenNorm {p : ℕ} (hp : 0 < p)
    {A : ℕ → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hA : ∀ n, MemSchattenClass (p : ℝ) (A n)) (hT : MemSchattenClass (p : ℝ) T)
    (hD : ∀ n, MemSchattenClass (p : ℝ) (A n - T))
    {C : ℝ} (hC1 : 1 ≤ C)
    (hCA : ∀ n, schattenNorm (p : ℝ) (A n) ≤ C)
    (htend : Tendsto (fun n => schattenNorm (p : ℝ) (A n - T)) atTop (nhds 0))
    {z : ℂ} (hz : ‖z‖ * (2 * C) < 1) :
    Tendsto (fun n => opSchattenDet p (A n) z) atTop (nhds (opSchattenDet p T z)) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hB1 : (1 : ℝ) ≤ 2 * C := by linarith
  have hbound : ∀ (n : ℕ) (k : ℕ),
      ‖(fun m => opTrace ((A n) ^ m)) (k + p)‖
        ≤ ((1 + (p : ℝ)) * C ^ (p : ℝ)) * (2 * C) ^ k :=
    fun n k => norm_opTrace_pow_add_le hp (hA n) hC1 (hCA n) k
  have hconv : ∀ k : ℕ, Tendsto (fun n => (fun m => opTrace ((A n) ^ m)) (k + p)) atTop
      (nhds ((fun m => opTrace (T ^ m)) (k + p))) := by
    intro k
    refine tendsto_opTrace_pow_of_tendsto_schattenNorm hpR hA hT hD hCA htend
      (k := k + p) (by omega) ?_
    push_cast
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  exact tendsto_tracePowerDet_of_tendsto hp hB1 hbound hconv hz

/-- **The closure of the determinant graph, with the operators presented in the Schatten
topology.**  A family of order-`p` determinants of Schatten-`p` operators, each multiplied by the
exponential of a normalized polynomial of bounded degree, converges only to the order-`p`
determinant of the Schatten limit times the exponential of a polynomial of the same shape. -/
theorem exists_poly_limit_of_tendsto_opSchattenDet {J p : ℕ} (hp : 0 < p)
    {A : ℕ → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hA : ∀ n, MemSchattenClass (p : ℝ) (A n)) (hT : MemSchattenClass (p : ℝ) T)
    (hD : ∀ n, MemSchattenClass (p : ℝ) (A n - T))
    {C : ℝ} (hC1 : 1 ≤ C)
    (hCA : ∀ n, schattenNorm (p : ℝ) (A n) ≤ C) (hCT : schattenNorm (p : ℝ) T ≤ C)
    (htend : Tendsto (fun n => schattenNorm (p : ℝ) (A n - T)) atTop (nhds 0))
    {r : ℝ} (hr : 0 < r) (hrB : r * (2 * C) < 1)
    {P : ℕ → Polynomial ℂ} (hdeg : ∀ n, (P n).natDegree ≤ J + 1)
    (hP0 : ∀ n, (P n).coeff 0 = 0)
    {v : Fin (J + 1) → ℂ} (hv : Function.Injective v) (hvU : ∀ i, v i ∈ ball (0 : ℂ) r)
    {F : ℂ → ℂ} {Fd : Fin (J + 1) → ℂ}
    (hFval : ∀ z ∈ ball (0 : ℂ) r, Tendsto
      (fun n => opSchattenDet p (A n) z * Complex.exp (Polynomial.eval z (P n))) atTop
      (nhds (F z)))
    (hFder : ∀ i, Tendsto
      (fun n => deriv (fun w : ℂ =>
        opSchattenDet p (A n) w * Complex.exp (Polynomial.eval w (P n))) (v i)) atTop
      (nhds (Fd i)))
    (hFne : ∀ i, F (v i) ≠ 0) :
    ∃ Q : Polynomial ℂ, Q.natDegree ≤ J + 1 ∧ Q.coeff 0 = 0 ∧
      (∀ h : ℕ, Tendsto (fun n => (P n).coeff h) atTop (nhds (Q.coeff h))) ∧
      ∀ z ∈ ball (0 : ℂ) r, F z = opSchattenDet p T z * Complex.exp (Polynomial.eval z Q) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hB1 : (1 : ℝ) ≤ 2 * C := by linarith
  have hS0 : (0 : ℝ) ≤ (1 + (p : ℝ)) * C ^ (p : ℝ) := by
    have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
    positivity
  have hbound : ∀ (n : ℕ) (k : ℕ),
      ‖(fun m => opTrace ((A n) ^ m)) (k + p)‖
        ≤ ((1 + (p : ℝ)) * C ^ (p : ℝ)) * (2 * C) ^ k :=
    fun n k => norm_opTrace_pow_add_le hp (hA n) hC1 (hCA n) k
  have hboundmu : ∀ k : ℕ,
      ‖(fun m => opTrace (T ^ m)) (k + p)‖
        ≤ ((1 + (p : ℝ)) * C ^ (p : ℝ)) * (2 * C) ^ k :=
    fun k => norm_opTrace_pow_add_le hp hT hC1 hCT k
  have hconv : ∀ k : ℕ, Tendsto (fun n => (fun m => opTrace ((A n) ^ m)) (k + p)) atTop
      (nhds ((fun m => opTrace (T ^ m)) (k + p))) := by
    intro k
    refine tendsto_opTrace_pow_of_tendsto_schattenNorm hpR hA hT hD hCA htend
      (k := k + p) (by omega) ?_
    push_cast
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  exact exists_poly_limit_of_tendsto_tracePowerDet hp hB1 hS0 hbound hboundmu hconv hr hrB
    hdeg hP0 hv hvU hFval hFder hFne

end

end GaloisForLFunctions.HTGeometry
